use rustc_middle::ty;
use rustc_middle::ty::TyCtxt;
use rustc_middle::mir::{TerminatorKind, Operand};
use rustc_data_structures::fx::FxHashSet;

use crate::rap_error;
use super::graph::*;
use super::log::*;
use super::bug_records::*;
use log::Log;

impl<'tcx> SafeDropGraph<'tcx>{
    // alias analysis for a single block
    pub fn alias_check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, move_set: &mut FxHashSet<usize>){
        for stmt in self.blocks[bb_index].const_value.clone(){
            self.constant.insert(stmt.0, stmt.1);
        }
        let cur_block = self.blocks[bb_index].clone();
        for i in cur_block.assignments{
            let mut l_node_ref = self.handle_projection(false, i.left.local.as_usize(), tcx, i.left.clone());
            let r_node_ref = self.handle_projection(true, i.right.local.as_usize(), tcx, i.right.clone());
            if i.atype == AssignType::Variant {
                self.vars[l_node_ref].alias[0] = r_node_ref;
                continue;
            }
            self.uaf_check(r_node_ref, i.span, i.right.local.as_usize(), false);
            self.fill_alive(l_node_ref, self.scc_indices[bb_index] as isize);
            if i.atype == AssignType::Field {
                l_node_ref = *self.vars[l_node_ref].sons.get(&0).unwrap() + 2;
                self.vars[l_node_ref].alive = self.scc_indices[bb_index] as isize;
                self.vars[l_node_ref-1].alive = self.scc_indices[bb_index] as isize;
                self.vars[l_node_ref-2].alive = self.scc_indices[bb_index] as isize;
            }
            merge_alias(move_set, l_node_ref, r_node_ref, &mut self.vars);
        }        
    }
    // interprocedure alias analysis, mainly handle the function call statement
    pub fn call_alias_check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, func_map: &mut FuncMap, move_set: &mut FxHashSet<usize>){
        let cur_block = self.blocks[bb_index].clone();
        for call in cur_block.calls{
            if let TerminatorKind::Call { ref func, ref args, ref destination, target:_, unwind: _, call_source: _, fn_span: _ } = call.kind {
                if let Operand::Constant(ref constant) = func {
                    let left_ssa = self.handle_projection(false, destination.local.as_usize(), tcx, destination.clone());
                    self.vars[left_ssa].alive = self.scc_indices[bb_index] as isize;
                    let mut merge_vec = Vec::new();
                    merge_vec.push(left_ssa);
                    let mut may_drop_flag = 0;
                    if self.vars[left_ssa].may_drop {
                        may_drop_flag += 1;
                    }
                    for arg in args {
                        match arg {
                            Operand::Copy(ref p) => {
                                let right_ssa = self.handle_projection(true, p.local.as_usize(), tcx, p.clone());
                                self.uaf_check(right_ssa, call.source_info.span, p.local.as_usize(), true);
                                merge_vec.push(right_ssa);
                                if self.vars[right_ssa].may_drop {
                                    may_drop_flag += 1;
                                }
                            },
                            Operand::Move(ref p) => {
                                let right_ssa = self.handle_projection(true, p.local.as_usize(), tcx, p.clone());
                                self.uaf_check(right_ssa, call.source_info.span, p.local.as_usize(), true);
                                merge_vec.push(right_ssa);
                                if self.vars[right_ssa].may_drop {
                                    may_drop_flag += 1;
                                }
                            },
                            Operand::Constant(_) => {
                                merge_vec.push(0);
                            },
                        }
                    }
                    if let ty::FnDef(ref target_id, _) = constant.const_.ty().kind() {
                        if may_drop_flag > 1 || (may_drop_flag > 0 && Self::should_check(target_id.clone()) == false){
                            if tcx.is_mir_available(*target_id){
                                if func_map.map.contains_key(&target_id.index.as_usize()){
                                    let assignments = func_map.map.get(&target_id.index.as_usize()).unwrap();
                                    for assign in assignments.assignments.iter(){
                                        if !assign.valuable(){
                                            continue;
                                        }
                                        merge(move_set, &mut self.vars, assign, &merge_vec);
                                    }
                                    for dead in assignments.dead.iter(){
                                        let drop = merge_vec[*dead];
                                        self.dead_node(drop, 99999, &call.source_info, false);
                                    }
                                }
                                else{
                                    if func_map.set.contains(&target_id.index.as_usize()){
                                        continue;
                                    }
                                    func_map.set.insert(target_id.index.as_usize());
                                    let func_body = tcx.optimized_mir(*target_id);
                                    let mut safedrop_graph = SafeDropGraph::new(&func_body, tcx, *target_id);
                                    safedrop_graph.solve_scc();
                                    safedrop_graph.check(0, tcx, func_map);
                                    let return_results = safedrop_graph.return_results.clone();
                                    for assign in return_results.assignments.iter(){
                                        if !assign.valuable(){
                                            continue;
                                        }
                                        merge(move_set, &mut self.vars, assign, &merge_vec);
                                    }
                                    for dead in return_results.dead.iter(){
                                        let drop = merge_vec[*dead];
                                        self.dead_node(drop, 99999, &call.source_info, false);
                                    }
                                    func_map.map.insert(target_id.index.as_usize(), return_results);
                                }
                            }
                            else{
                                if self.vars[left_ssa].may_drop{
                                    if self.corner_handle(left_ssa, &merge_vec, move_set, *target_id){
                                        continue;
                                    }
                                    let mut right_set = Vec::new(); 
                                    for right_ssa in &merge_vec{
                                        if self.vars[*right_ssa].may_drop && left_ssa != *right_ssa && self.vars[left_ssa].is_ptr(){
                                            right_set.push(*right_ssa);
                                        }
                                    }
                                    if right_set.len() == 1{
                                        merge_alias(move_set, left_ssa, right_set[0], &mut self.vars);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[derive(Debug,Clone)]
pub struct ReturnAssign{
    pub left_index: usize,
    pub left: Vec<usize>,
    pub left_may_drop: bool, 
    pub left_need_drop: bool,
    pub right_index: usize,
    pub right: Vec<usize>,
    pub right_may_drop: bool, 
    pub right_need_drop: bool,
    pub atype: usize,
}

impl ReturnAssign{
    pub fn new(atype: usize, left_index: usize, left_may_drop: bool, left_need_drop: bool,
        right_index: usize, right_may_drop: bool, right_need_drop: bool) -> ReturnAssign{
        let left = Vec::<usize>::new();
        let right = Vec::<usize>::new();
        ReturnAssign{
            left_index: left_index,
            left: left,
            left_may_drop: left_may_drop,
            left_need_drop: left_need_drop,
            right_index: right_index,
            right: right,
            right_may_drop: right_may_drop,
            right_need_drop: right_need_drop,
            atype: atype
        }
    }

    pub fn valuable(&self) -> bool{
        return self.left_may_drop && self.right_may_drop;
    }
}

#[derive(Debug, Clone)]
pub struct ReturnResults{
    pub arg_size: usize,
    pub assignments: Vec<ReturnAssign>,
    pub dead: FxHashSet<usize>,
}

impl ReturnResults {
    pub fn new(arg_size: usize) -> ReturnResults{
        let assignments = Vec::<ReturnAssign>::new();
        let dead = FxHashSet::default();
        ReturnResults { arg_size: arg_size, assignments: assignments, dead: dead }
    }
}
//instruction to assign alias for a variable.
pub fn merge_alias(move_set: &mut FxHashSet<usize>, left_ssa: usize, right_ssa: usize, nodes: &mut Vec<Var>){
    if nodes[left_ssa].index == nodes[right_ssa].index{
        return;
    }
    if move_set.contains(&left_ssa){
        let mut alias_clone = nodes[right_ssa].alias.clone();
        nodes[left_ssa].alias.append(&mut alias_clone);
    }
    else{
        move_set.insert(left_ssa);
        nodes[left_ssa].alias = nodes[right_ssa].alias.clone();
    }
    for son in nodes[right_ssa].sons.clone().into_iter(){
        if nodes[left_ssa].sons.contains_key(&son.0) == false{
            let mut node = Var::new(nodes[left_ssa].index, nodes.len(), nodes[son.1].need_drop, nodes[son.1].may_drop);
            node.kind = nodes[son.1].kind;
            node.alive = nodes[left_ssa].alive;
            node.field_info = nodes[left_ssa].field_info.clone();
            node.field_info.push(son.0);
            nodes[left_ssa].sons.insert(son.0, node.local);
            nodes.push(node);
        }
        let l_son = *(nodes[left_ssa].sons.get(&son.0).unwrap());
        merge_alias(move_set, l_son, son.1, nodes);
    }
}

//inter-procedure instruction to merge alias.
pub fn merge(move_set: &mut FxHashSet<usize>, nodes: &mut Vec<Var>, assign: &ReturnAssign, arg_vec: &Vec<usize>) {
    if assign.left_index >= arg_vec.len() {
        rap_error!("Vector error!");
        return;
    }
    if assign.right_index >= arg_vec.len(){
        rap_error!("Vector error!");
        return;
    }
    let left_init = arg_vec[assign.left_index];
    let mut right_init = arg_vec[assign.right_index];
    let mut left_ssa = left_init;
    let mut right_ssa = right_init;
    for index in assign.left.iter() {
        if nodes[left_ssa].sons.contains_key(&index) == false {
            let need_drop = assign.left_need_drop;
            let may_drop = assign.left_may_drop;
            let mut node = Var::new(left_init, nodes.len(), need_drop, may_drop);
            node.kind = 1;
            node.alive = nodes[left_ssa].alive;
            node.field_info = nodes[left_ssa].field_info.clone();
            node.field_info.push(*index);
            nodes[left_ssa].sons.insert(*index, node.local);
            nodes.push(node);
        }
        left_ssa = *nodes[left_ssa].sons.get(&index).unwrap();
    }
    for index in assign.right.iter() {
        if nodes[right_ssa].alias[0] != right_ssa {
            right_ssa = nodes[right_ssa].alias[0];
            right_init = nodes[right_ssa].index;
        }
        if nodes[right_ssa].sons.contains_key(&index) == false {
            let need_drop = assign.right_need_drop;
            let may_drop = assign.right_may_drop;
            let mut node = Var::new(right_init, nodes.len(), need_drop, may_drop);
            node.kind = 1;
            node.alive = nodes[right_ssa].alive;
            node.field_info = nodes[right_ssa].field_info.clone();
            node.field_info.push(*index);
            nodes[right_ssa].sons.insert(*index, node.local);
            nodes.push(node);
        }
        right_ssa = *nodes[right_ssa].sons.get(&index).unwrap();
    }
    merge_alias(move_set, left_ssa, right_ssa, nodes);
}
