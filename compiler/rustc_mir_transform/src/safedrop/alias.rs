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
            let mut l_node_ref = self.handle_projection(false, i.lv.local.as_usize(), tcx, i.lv.clone());
            let r_node_ref = self.handle_projection(true, i.rv.local.as_usize(), tcx, i.rv.clone());
            if i.atype == AssignType::Variant {
                self.values[l_node_ref].alias[0] = r_node_ref;
                continue;
            }
            self.uaf_check(r_node_ref, i.span, i.rv.local.as_usize(), false);
            self.fill_alive(l_node_ref, self.scc_indices[bb_index] as isize);
            if i.atype == AssignType::Field {
                l_node_ref = *self.values[l_node_ref].fields.get(&0).unwrap() + 2;
                self.values[l_node_ref].alive = self.scc_indices[bb_index] as isize;
                self.values[l_node_ref-1].alive = self.scc_indices[bb_index] as isize;
                self.values[l_node_ref-2].alive = self.scc_indices[bb_index] as isize;
            }
            merge_alias(move_set, l_node_ref, r_node_ref, &mut self.values);
        }        
    }
    // interprocedure alias analysis, mainly handle the function call statement
    pub fn call_alias_check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, func_map: &mut FuncMap, move_set: &mut FxHashSet<usize>){
        let cur_block = self.blocks[bb_index].clone();
        for call in cur_block.calls{
            if let TerminatorKind::Call { ref func, ref args, ref destination, target:_, unwind: _, call_source: _, fn_span: _ } = call.kind {
                if let Operand::Constant(ref constant) = func {
                    let lv = self.handle_projection(false, destination.local.as_usize(), tcx, destination.clone());
                    self.values[lv].alive = self.scc_indices[bb_index] as isize;
                    let mut merge_vec = Vec::new();
                    merge_vec.push(lv);
                    let mut may_drop_flag = 0;
                    if self.values[lv].may_drop {
                        may_drop_flag += 1;
                    }
                    for arg in args {
                        match arg {
                            Operand::Copy(ref p) => {
                                let rv = self.handle_projection(true, p.local.as_usize(), tcx, p.clone());
                                self.uaf_check(rv, call.source_info.span, p.local.as_usize(), true);
                                merge_vec.push(rv);
                                if self.values[rv].may_drop {
                                    may_drop_flag += 1;
                                }
                            },
                            Operand::Move(ref p) => {
                                let rv = self.handle_projection(true, p.local.as_usize(), tcx, p.clone());
                                self.uaf_check(rv, call.source_info.span, p.local.as_usize(), true);
                                merge_vec.push(rv);
                                if self.values[rv].may_drop {
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
                                        merge(move_set, &mut self.values, assign, &merge_vec);
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
                                        merge(move_set, &mut self.values, assign, &merge_vec);
                                    }
                                    for dead in return_results.dead.iter(){
                                        let drop = merge_vec[*dead];
                                        self.dead_node(drop, 99999, &call.source_info, false);
                                    }
                                    func_map.map.insert(target_id.index.as_usize(), return_results);
                                }
                            }
                            else{
                                if self.values[lv].may_drop{
                                    if self.corner_handle(lv, &merge_vec, move_set, *target_id){
                                        continue;
                                    }
                                    let mut right_set = Vec::new(); 
                                    for rv in &merge_vec{
                                        if self.values[*rv].may_drop && lv != *rv && self.values[lv].is_ptr(){
                                            right_set.push(*rv);
                                        }
                                    }
                                    if right_set.len() == 1{
                                        merge_alias(move_set, lv, right_set[0], &mut self.values);
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
pub fn merge_alias(move_set: &mut FxHashSet<usize>, lv: usize, rv: usize, nodes: &mut Vec<ValueNode>){
    if nodes[lv].index == nodes[rv].index{
        return;
    }
    if move_set.contains(&lv){
        let mut alias_clone = nodes[rv].alias.clone();
        nodes[lv].alias.append(&mut alias_clone);
    }
    else{
        move_set.insert(lv);
        nodes[lv].alias = nodes[rv].alias.clone();
    }
    for son in nodes[rv].fields.clone().into_iter(){
        if nodes[lv].fields.contains_key(&son.0) == false {
            let mut node = ValueNode::new(nodes[lv].index, nodes.len(), nodes[son.1].need_drop, nodes[son.1].may_drop);
            node.kind = nodes[son.1].kind;
            node.alive = nodes[lv].alive;
            node.field_info = nodes[lv].field_info.clone();
            node.field_info.push(son.0);
            nodes[lv].fields.insert(son.0, node.local);
            nodes.push(node);
        }
        let l_son = *(nodes[lv].fields.get(&son.0).unwrap());
        merge_alias(move_set, l_son, son.1, nodes);
    }
}

//inter-procedure instruction to merge alias.
pub fn merge(move_set: &mut FxHashSet<usize>, nodes: &mut Vec<ValueNode>, assign: &ReturnAssign, arg_vec: &Vec<usize>) {
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
    let mut lv = left_init;
    let mut rv = right_init;
    for index in assign.left.iter() {
        if nodes[lv].fields.contains_key(&index) == false {
            let need_drop = assign.left_need_drop;
            let may_drop = assign.left_may_drop;
            let mut node = ValueNode::new(left_init, nodes.len(), need_drop, may_drop);
            node.kind = 1;
            node.alive = nodes[lv].alive;
            node.field_info = nodes[lv].field_info.clone();
            node.field_info.push(*index);
            nodes[lv].fields.insert(*index, node.local);
            nodes.push(node);
        }
        lv = *nodes[lv].fields.get(&index).unwrap();
    }
    for index in assign.right.iter() {
        if nodes[rv].alias[0] != rv {
            rv = nodes[rv].alias[0];
            right_init = nodes[rv].index;
        }
        if nodes[rv].fields.contains_key(&index) == false {
            let need_drop = assign.right_need_drop;
            let may_drop = assign.right_may_drop;
            let mut node = ValueNode::new(right_init, nodes.len(), need_drop, may_drop);
            node.kind = 1;
            node.alive = nodes[rv].alive;
            node.field_info = nodes[rv].field_info.clone();
            node.field_info.push(*index);
            nodes[rv].fields.insert(*index, node.local);
            nodes.push(node);
        }
        rv = *nodes[rv].fields.get(&index).unwrap();
    }
    merge_alias(move_set, lv, rv, nodes);
}
