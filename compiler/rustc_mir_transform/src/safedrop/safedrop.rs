//This module should put under the directory: rust/compiler/rustc_mir_transform/safedrop_check

use rustc_middle::ty::TyCtxt;
use rustc_middle::ty;
use rustc_middle::mir::TerminatorKind;
use rustc_middle::mir::Operand;
use rustc_middle::mir::Operand::{Copy, Move, Constant};
use rustc_data_structures::fx::FxHashSet;

use crate::{rap_error, RapLogLevel, record_msg, RAP_LOGGER};
use log::Log;

use super::graph::*;
use super::bug_records::*;
use super::alias::*;

pub const DROP:usize = 1634;
pub const DROP_IN_PLACE:usize = 2160;
pub const CALL_MUT:usize = 3022;
pub const NEXT:usize = 7587;

pub const VISIT_LIMIT:usize = 10000;

impl<'tcx> SafeDropGraph<'tcx>{
    // alias analysis for a single block
    pub fn alias_check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, move_set: &mut FxHashSet<usize>){
        for stmt in self.blocks[bb_index].const_value.clone(){
            self.constant_bool.insert(stmt.0, stmt.1);
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
    // analyze the drop statement and update the alive state for nodes.
    pub fn drop_check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>){
        let cur_block = self.blocks[bb_index].clone();
        for drop in cur_block.drops{
            match drop.kind{
                TerminatorKind::Drop{ref place, target: _, unwind: _, replace: _} => {
                    let life_begin = self.scc_indices[bb_index];
                    let drop_local = self.handle_projection(false, place.local.as_usize(), tcx, place.clone());
                    let info = drop.source_info.clone();
                    self.dead_node(drop_local, life_begin, &info, false);
                },
                TerminatorKind::Call { func: _,  ref args, .. } => {
                    if args.len() > 0 {
                        let life_begin = self.scc_indices[bb_index];
                    	let place = match args[0] {
                        	Operand::Copy(place) => place,
                        	Operand::Move(place) => place,
                        	_ => { rap_error!("Constant operand exists: {:?}", args[0]); return; }
                    	};
                    	let drop_local = self.handle_projection(false, place.local.as_usize(), tcx, place.clone());
                    	let info = drop.source_info.clone();
                    	self.dead_node(drop_local, life_begin, &info, false);
		    }
                },
                _ => {}
            }
        }
    }

    // the core function of the safedrop.
    pub fn check(&mut self, bb_index: usize, tcx: TyCtxt<'tcx>, func_map: &mut FuncMap) {
        self.visit_times += 1;
        if self.visit_times > VISIT_LIMIT {
            return;
        }
        let cur_block = self.blocks[self.scc_indices[bb_index]].clone();
        let mut move_set = FxHashSet::default();
        self.alias_check(self.scc_indices[bb_index], tcx, &mut move_set);
        self.call_alias_check(self.scc_indices[bb_index], tcx, func_map, &mut move_set);
        self.drop_check(self.scc_indices[bb_index], tcx);

        /* Handle cases if the current block is a merged scc block with sub block */
        if cur_block.scc_sub_blocks.len() > 0{
            for i in cur_block.scc_sub_blocks.clone(){
                self.alias_check(i, tcx, &mut move_set);
                self.call_alias_check(i, tcx,  func_map, &mut move_set);
                self.drop_check(i, tcx);
            }
        }

        /* Reach a leaf node, check bugs */
        if cur_block.next.len() == 0 {
            // check the bugs.
            if Self::should_check(self.def_id){
                self.bug_check(&cur_block);
            }
            // merge the result.
            let results_nodes = self.vars.clone();
            self.merge_results(results_nodes, cur_block.is_cleanup);
            return;
        }

        
        //search for the next block to visit.
        let mut loop_flag = true;
        let mut ans_bool = 0;
        let mut s_target = 0;
        let mut discr_target = 0;
        let mut s_targets = None;
        //handle the SwitchInt statement.
        if cur_block.switch_stmts.is_empty() == false && cur_block.scc_sub_blocks.is_empty() {
            if let TerminatorKind::SwitchInt { ref discr, ref targets } = cur_block.switch_stmts[0].clone().kind {
                match discr {
                    Copy(p) | Move(p) => {
                        let place = self.handle_projection(false, p.local.as_usize(), tcx, p.clone());
                        if let Some(const_bool) = self.constant_bool.get(&self.vars[place].alias[0]) {
                            loop_flag = false;
                            ans_bool = *const_bool;
                        }
                        if self.vars[place].alias[0] != place{
                            discr_target = self.vars[place].alias[0];
                            s_targets = Some(targets.clone());
                        }
                    } 
                    Constant(c) => {
                        loop_flag = false;
                        let param_env = tcx.param_env(self.def_id);
                        ans_bool = c.const_.eval_target_usize(tcx, param_env) as usize;
                    }
                }
                if !loop_flag {
                    for iter in targets.iter() {
                        if iter.0 as usize == ans_bool as usize {
                            s_target = iter.1.as_usize();
                            break;
                        }
                    }
                    if s_target == 0 {
                        let all_target = targets.all_targets();
                        if ans_bool as usize >= all_target.len(){
                            s_target = all_target[all_target.len()-1].as_usize();
                        } else {
                            s_target = all_target[ans_bool as usize].as_usize();
                        }
                    }
                }
            }
        }
        // only one path
        if cur_block.next.len() == 1 {
            for next in cur_block.next { // looped only once; we cannot use [0] for FxHashSet.
                self.check(next, tcx, func_map);
            }
        } else {
            // fixed path since a constant switchInt value
            if loop_flag == false {
                self.check(s_target, tcx, func_map);
            } else {
                // Other cases in switchInt terminators
                if let Some(targets) = s_targets {
                    for iter in targets.iter(){
                        if self.visit_times > VISIT_LIMIT {
                            continue;
                        }
                        let next_index = iter.1.as_usize();
                        let backup_nodes = self.vars.clone();
                        let constant_record = self.constant_bool.clone();
                        self.constant_bool.insert(discr_target , iter.0 as usize);
                        self.check(next_index, tcx, func_map);
                        self.vars = backup_nodes;
                        self.constant_bool = constant_record;
                    }
                    let all_targets = targets.all_targets();
                    let next_index = all_targets[all_targets.len()-1].as_usize();
                    let backup_nodes = self.vars.clone();
                    let constant_record = self.constant_bool.clone();
                    self.constant_bool.insert(discr_target , 99999 as usize);
                    self.check(next_index, tcx, func_map);
                    self.vars = backup_nodes;
                    self.constant_bool = constant_record;
                } else {
                    for i in cur_block.next {
                        if self.visit_times > VISIT_LIMIT {
                            continue;
                        }
                        let next_index = i;
                        let backup_nodes = self.vars.clone();
                        let constant_record = self.constant_bool.clone();
                        self.check(next_index, tcx, func_map);
                        self.vars = backup_nodes;
                        self.constant_bool = constant_record;
                    }
                }
            }
        }
    }
}
