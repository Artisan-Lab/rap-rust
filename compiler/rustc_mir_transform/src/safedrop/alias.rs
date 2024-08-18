use rustc_middle::ty;
use rustc_middle::ty::TyCtxt;
use rustc_middle::mir::{TerminatorKind, Operand, Place, ProjectionElem};
use rustc_data_structures::fx::FxHashSet;

use crate::rap_error;
use super::graph::*;
use super::types::*;
use super::log::*;
use super::bug_records::*;
use log::Log;

impl<'tcx> SafeDropGraph<'tcx>{
    /* alias analysis for a single block */
    pub fn alias_bb(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, move_set: &mut FxHashSet<usize>) {
        for stmt in self.blocks[bb_index].const_value.clone() {
            self.constant.insert(stmt.0, stmt.1);
        }
        let cur_block = self.blocks[bb_index].clone();
        for assign in cur_block.assignments {
            let mut lv_aliaset_idx = self.handle_projection(tcx, false, assign.lv.clone());
            let rv_aliaset_idx = self.handle_projection(tcx, true, assign.rv.clone());
            if assign.atype == AssignType::Variant {
                self.values[lv_aliaset_idx].alias[0] = rv_aliaset_idx;
                continue;
            }
            self.uaf_check(rv_aliaset_idx, assign.span, assign.rv.local.as_usize(), false);
            self.fill_birth(lv_aliaset_idx, self.scc_indices[bb_index] as isize);
            
            if assign.atype == AssignType::InitBox {
                lv_aliaset_idx = *self.values[lv_aliaset_idx].fields.get(&0).unwrap();
                self.values[lv_aliaset_idx].birth = self.scc_indices[bb_index] as isize;
            }
            merge_alias(move_set, lv_aliaset_idx, rv_aliaset_idx, &mut self.values);
        }        
    }

    /* Check the aliases introduced by the terminators (function call) of a scc block */
    pub fn alias_bbcall(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, func_map: &mut FuncMap, move_set: &mut FxHashSet<usize>){
        let cur_block = self.blocks[bb_index].clone();
        for call in cur_block.calls {
            if let TerminatorKind::Call { ref func, ref args, ref destination, target:_, unwind: _, call_source: _, fn_span: _ } = call.kind {
                if let Operand::Constant(ref constant) = func {
                    let lv = self.handle_projection(tcx, false, destination.clone());
                    self.values[lv].birth = self.scc_indices[bb_index] as isize;
                    let mut merge_vec = Vec::new();
                    merge_vec.push(lv);
                    let mut may_drop_flag = 0;
                    if self.values[lv].may_drop {
                        may_drop_flag += 1;
                    }
                    for arg in args {
                        match arg {
                            Operand::Copy(ref p) => {
                                let rv = self.handle_projection(tcx, true, p.clone());
                                self.uaf_check(rv, call.source_info.span, p.local.as_usize(), true);
                                merge_vec.push(rv);
                                if self.values[rv].may_drop {
                                    may_drop_flag += 1;
                                }
                            },
                            Operand::Move(ref p) => {
                                let rv = self.handle_projection(tcx, true, p.clone());
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
                        if may_drop_flag > 1 || (may_drop_flag > 0 && Self::should_check(target_id.clone()) == false) {
                            if tcx.is_mir_available(*target_id) {
                                if func_map.map.contains_key(&target_id.index.as_usize()) {
                                    let assignments = func_map.map.get(&target_id.index.as_usize()).unwrap();
                                    for assign in assignments.alias_vec.iter() {
                                        if !assign.valuable() {
                                            continue;
                                        }
                                        merge(move_set, &mut self.values, assign, &merge_vec);
                                    }
                                    for dead in assignments.dead.iter() {
                                        let drop = merge_vec[*dead];
                                        self.dead_node(drop, 99999, &call.source_info, false);
                                    }
                                }
                                else{
                                    if func_map.set.contains(&target_id.index.as_usize()) {
                                        continue;
                                    }
                                    func_map.set.insert(target_id.index.as_usize());
                                    let func_body = tcx.optimized_mir(*target_id);
                                    let mut safedrop_graph = SafeDropGraph::new(&func_body, tcx, *target_id);
                                    safedrop_graph.solve_scc();
                                    safedrop_graph.check(0, tcx, func_map);
                                    let ret_alias = safedrop_graph.ret_alias.clone();
                                    for assign in ret_alias.alias_vec.iter() {
                                        if !assign.valuable(){
                                            continue;
                                        }
                                        merge(move_set, &mut self.values, assign, &merge_vec);
                                    }
                                    for dead in ret_alias.dead.iter() {
                                        let drop = merge_vec[*dead];
                                        self.dead_node(drop, 99999, &call.source_info, false);
                                    }
                                    func_map.map.insert(target_id.index.as_usize(), ret_alias);
                                }
                            }
                            else {
                                if self.values[lv].may_drop {
                                    if self.corner_handle(lv, &merge_vec, move_set, *target_id){
                                        continue;
                                    }
                                    let mut right_set = Vec::new(); 
                                    for rv in &merge_vec {
                                        if self.values[*rv].may_drop && lv != *rv && self.values[lv].is_ptr(){
                                            right_set.push(*rv);
                                        }
                                    }
                                    if right_set.len() == 1 {
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

    // assign to the variable _x, we will set the birth of _x and its child nodes a new birth.
    pub fn fill_birth(&mut self, node: usize, birth: isize) {
        self.values[node].birth = birth;
        //TODO: check the correctness.
        for i in self.values[node].alias.clone() {
            if self.values[i].birth == -1 {
                self.values[i].birth = birth;
            }
        }
        for i in self.values[node].fields.clone().into_iter() {
            self.fill_birth(i.1, birth); //i.1 corresponds to the local field.
        }
    }

    /*
     * This is the function for field sensitivity
     * If the projection is a deref, we directly return its head alias or alias[0].
     * If the id is not a ref, we further make the id and its first element an alias, i.e., level-insensitive
     *
     */
    pub fn handle_projection(&mut self, tcx: TyCtxt<'tcx>, is_right: bool, place: Place<'tcx>) -> usize {
        let mut index = place.local.as_usize();
        let mut cur_local = index;
        for proj in place.projection {
            let new_id = self.values.len();
            match proj {
                ProjectionElem::Deref => {
                    if cur_local != self.values[cur_local].alias[0] {
                        cur_local = self.values[cur_local].alias[0];
                    } else if self.values[cur_local].is_ref() == false {
                        let mut node = ValueNode::new(new_id, new_id, true, true);
                        node.kind = 1;
                        node.birth = self.values[cur_local].birth;
                        self.values[cur_local].alias[0] = new_id;
                        self.values.push(node);
                    }
                }
                /*
                 * 2 = 1.0; 0 = 2.0; => 0 = 1.0.0
                 */
                ProjectionElem::Field(field, ty) => {
                    if is_right && self.values[cur_local].alias[0] != cur_local {
                        cur_local = self.values[cur_local].alias[0];
                        index = self.values[cur_local].index;
                    }
                    let field_idx = field.as_usize();
                    if self.values[cur_local].fields.contains_key(&field_idx) == false {
                        let param_env = tcx.param_env(self.def_id);
                        let need_drop = ty.needs_drop(tcx, param_env);
                        let may_drop = !is_not_drop(tcx, ty);
                        let mut node = ValueNode::new(index, new_id, need_drop, need_drop || may_drop);
                        node.kind = kind(ty);
                        node.birth = self.values[cur_local].birth;
                        node.field_info = self.values[cur_local].field_info.clone();
                        node.field_info.push(field_idx);
                        self.values[cur_local].fields.insert(field_idx, node.local);
                        self.values.push(node);
                    }
                    cur_local = *self.values[cur_local].fields.get(&field_idx).unwrap();
                }
                _ => {}
            }
        }
        return cur_local;
    }
}
/*
 * To store the alias relationships among arguments and return values.
 */
#[derive(Debug,Clone)]
pub struct RetAlias{
    pub left_index: usize,
    pub left: Vec<usize>, //field
    pub left_may_drop: bool, 
    pub left_need_drop: bool,
    pub right_index: usize,
    pub right: Vec<usize>,
    pub right_may_drop: bool, 
    pub right_need_drop: bool,
    pub atype: usize,
}

impl RetAlias{
    pub fn new(atype: usize, left_index: usize, left_may_drop: bool, left_need_drop: bool,
        right_index: usize, right_may_drop: bool, right_need_drop: bool) -> RetAlias{
        let left = Vec::<usize>::new();
        let right = Vec::<usize>::new();
        RetAlias{
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

/*
 * To store the alias relationships among arguments and return values.
 * Each function may have multiple return instructions, leading to different RetAlias.
 */
#[derive(Debug, Clone)]
pub struct FnRetAlias {
    pub arg_size: usize,
    pub alias_vec: Vec<RetAlias>,
    pub dead: FxHashSet<usize>,
}

impl FnRetAlias {
    pub fn new(arg_size: usize) -> FnRetAlias{
        let alias_vec = Vec::<RetAlias>::new();
        let dead = FxHashSet::default();
        FnRetAlias { arg_size: arg_size, alias_vec: alias_vec, dead: dead }
    }
}

//instruction to assign alias for a variable.
pub fn merge_alias(move_set: &mut FxHashSet<usize>, lv: usize, rv: usize, nodes: &mut Vec<ValueNode>) {
    if nodes[lv].index == nodes[rv].index {
        return;
    }
    if move_set.contains(&lv) {
        let mut alias_clone = nodes[rv].alias.clone();
        nodes[lv].alias.append(&mut alias_clone);
    } else {
        move_set.insert(lv);
        nodes[lv].alias = nodes[rv].alias.clone();
    }
    for son in nodes[rv].fields.clone().into_iter(){
        if nodes[lv].fields.contains_key(&son.0) == false {
            let mut node = ValueNode::new(nodes[lv].index, nodes.len(), nodes[son.1].need_drop, nodes[son.1].may_drop);
            node.kind = nodes[son.1].kind;
            node.birth = nodes[lv].birth;
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
pub fn merge(move_set: &mut FxHashSet<usize>, nodes: &mut Vec<ValueNode>, ret_alias: &RetAlias, arg_vec: &Vec<usize>) {
    if ret_alias.left_index >= arg_vec.len() || ret_alias.right_index >= arg_vec.len() {
        rap_error!("Vector error!");
        return;
    }
    let left_init = arg_vec[ret_alias.left_index];
    let mut right_init = arg_vec[ret_alias.right_index];
    let mut lv = left_init;
    let mut rv = right_init;
    for index in ret_alias.left.iter() {
        if nodes[lv].fields.contains_key(&index) == false {
            let need_drop = ret_alias.left_need_drop;
            let may_drop = ret_alias.left_may_drop;
            let mut node = ValueNode::new(left_init, nodes.len(), need_drop, may_drop);
            node.kind = 1;
            node.birth = nodes[lv].birth;
            node.field_info = nodes[lv].field_info.clone();
            node.field_info.push(*index);
            nodes[lv].fields.insert(*index, node.local);
            nodes.push(node);
        }
        lv = *nodes[lv].fields.get(&index).unwrap();
    }
    for index in ret_alias.right.iter() {
        if nodes[rv].alias[0] != rv {
            rv = nodes[rv].alias[0];
            right_init = nodes[rv].index;
        }
        if nodes[rv].fields.contains_key(&index) == false {
            let need_drop = ret_alias.right_need_drop;
            let may_drop = ret_alias.right_may_drop;
            let mut node = ValueNode::new(right_init, nodes.len(), need_drop, may_drop);
            node.kind = 1;
            node.birth = nodes[rv].birth;
            node.field_info = nodes[rv].field_info.clone();
            node.field_info.push(*index);
            nodes[rv].fields.insert(*index, node.local);
            nodes.push(node);
        }
        rv = *nodes[rv].fields.get(&index).unwrap();
    }
    merge_alias(move_set, lv, rv, nodes);
}
