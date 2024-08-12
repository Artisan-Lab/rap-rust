use rustc_middle::mir::{SourceInfo, Place, ProjectionElem};
use rustc_middle::ty::{TyCtxt};
use rustc_span::Span;
use rustc_span::symbol::Symbol;
use rustc_data_structures::fx::FxHashSet;
use super::graph::*;
use super::utils::*;
use super::types::*;
use super::alias::*;

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn report_bugs(&self) {
	    let filename = get_filename(self.tcx, self.def_id);
        match filename {
	        Some(filename) => {if filename.contains(".cargo") { return; }},
            None => {},
        }
        if self.bug_records.is_bug_free(){
            return;
        }
        let fn_name = match get_fn_name(self.tcx, self.def_id) {
            Some(name) => name,
            None => Symbol::intern("no symbol available"),
        };
        self.bug_records.df_bugs_output(fn_name);
        self.bug_records.uaf_bugs_output(fn_name);
        self.bug_records.dp_bug_output(fn_name);
    }

    // assign to the variable _x, we will set the alive of _x and its child nodes a new alive.
    pub fn fill_alive(&mut self, node: usize, alive: isize) {
        self.vars[node].alive = alive;
        //TODO: check the correctness.
        for i in self.vars[node].alias.clone() {
            if self.vars[i].alive == -1{
                self.vars[i].alive = alive;
            }
        }
        for i in self.vars[node].sons.clone().into_iter() {
            self.fill_alive(i.1, alive);
        }
    }

    pub fn exist_dead(&self, node: usize, record: &mut FxHashSet<usize>, dangling: bool) -> bool {
        //if is a dangling pointer check, only check the pointer type varible.
        if self.vars[node].is_alive() == false && (dangling && self.vars[node].is_ptr() || !dangling) {
            return true; 
        }
        record.insert(node);
        if self.vars[node].alias[0] != node{
            for i in self.vars[node].alias.clone().into_iter(){
                if i != node && record.contains(&i) == false && self.exist_dead(i, record, dangling) {
                    return true;
                }
            }
        }
        for i in self.vars[node].sons.clone().into_iter() {
            if record.contains(&i.1) == false && self.exist_dead(i.1, record, dangling) {
                return true;
            }
        }
        return false;
    }

    pub fn df_check(&mut self, drop: usize, span: Span) -> bool {
        let root = self.vars[drop].index;
        if self.vars[drop].is_alive() == false 
        && self.bug_records.df_bugs.contains_key(&root) == false {
            self.bug_records.df_bugs.insert(root, span.clone());
        }
        return self.vars[drop].is_alive() == false;
    }

    pub fn uaf_check(&mut self, used: usize, span: Span, origin: usize, is_func_call: bool) {
        let mut record = FxHashSet::default();
        if self.vars[used].may_drop && (!self.vars[used].is_ptr() || self.vars[used].index != origin || is_func_call)
        && self.exist_dead(used, &mut record, false) == true 
        && self.bug_records.uaf_bugs.contains(&span) == false {            
            self.bug_records.uaf_bugs.insert(span.clone());
        }
    }

    pub fn is_dangling(&self, local: usize) -> bool {
        let mut record = FxHashSet::default();
        return self.exist_dead(local, &mut record, local != 0);
    }

    pub fn dp_check(&mut self, current_block: &BlockNode<'tcx>) {
        match current_block.is_cleanup {
            true => {
                for i in 0..self.arg_size{
                    if self.vars[i+1].is_ptr() && self.is_dangling(i+1) {
                        self.bug_records.dp_bugs_unwind.insert(self.span);
                    }
                }
            },
            false => { 
                if self.vars[0].may_drop && self.is_dangling(0){
                    self.bug_records.dp_bugs.insert(self.span);
                } else{
                    for i in 0..self.arg_size {
                        if self.vars[i+1].is_ptr() && self.is_dangling(i+1) {
                            self.bug_records.dp_bugs.insert(self.span);
                        }
                    }
                }
            },
        }
    }

    pub fn dead_node(&mut self, drop: usize, life_begin: usize, info: &SourceInfo, alias: bool) {
        //Rc drop
        if self.vars[drop].is_corner_case() {
            return;
        } 
        //check if there is a double free bug.
        if self.df_check(drop, info.span) {
            return;
        }
        //drop their alias
        if self.vars[drop].alias[0] != drop {
            for i in self.vars[drop].alias.clone().into_iter() {
                if self.vars[i].is_ref(){
                    continue;
                }
                self.dead_node(i, life_begin, info, true);
            }
        }
        //drop the sons of the root node.
        //alias flag is used to avoid the sons of the alias are dropped repeatly.
        if alias == false {
            for i in self.vars[drop].sons.clone().into_iter() {
                if self.vars[drop].is_tuple() == true && self.vars[i.1].need_drop == false {
                    continue;
                } 
                self.dead_node( i.1, life_begin, info, false);
            }
        }
        //SCC.
        if self.vars[drop].alive < life_begin as isize && self.vars[drop].may_drop {
            self.vars[drop].dead();   
        }
    }

    // field-sensitive fetch instruction for a variable.
    // is_right: 2 = 1.0; 0 = 2.0; => 0 = 1.0.0;   
    pub fn handle_projection(&mut self, is_right: bool, local: usize, tcx: TyCtxt<'tcx>, place: Place<'tcx>) -> usize {
        let mut init_local = local;
        let mut current_local = local;
        for projection in place.projection{
            match projection{
                ProjectionElem::Deref => {
                    if current_local == self.vars[current_local].alias[0] && self.vars[current_local].is_ref() == false{
                        let need_drop = true;
                        let may_drop = true;
                        let mut node = Var::new(self.vars.len(), self.vars.len(), need_drop, may_drop);
                        node.kind = 1; //TODO
                        node.alive = self.vars[current_local].alive;
                        self.vars[current_local].alias[0] = self.vars.len();
                        self.vars.push(node);
                    }
                    current_local = self.vars[current_local].alias[0];
                    init_local = self.vars[current_local].index;
                }
                ProjectionElem::Field(field, ty) =>{
                    let index = field.as_usize();
                    if is_right && self.vars[current_local].alias[0] != current_local {
                        current_local = self.vars[current_local].alias[0];
                        init_local = self.vars[current_local].index;
                    }
                    if self.vars[current_local].sons.contains_key(&index) == false {
                        let param_env = tcx.param_env(self.def_id);
                        let need_drop = ty.needs_drop(tcx, param_env);
                        let may_drop = !is_not_drop(tcx, ty);
                        let mut node = Var::new(init_local, self.vars.len(), need_drop, need_drop || may_drop);
                        node.kind = kind(ty);
                        node.alive = self.vars[current_local].alive;
                        node.field_info = self.vars[current_local].field_info.clone();
                        node.field_info.push(index);
                        self.vars[current_local].sons.insert(index, node.local);
                        self.vars.push(node);
                    }
                    current_local = *self.vars[current_local].sons.get(&index).unwrap();
                }
                _ => {}
            }
        }
        return current_local;
    }

    //merge the result of current path to the final result.
    pub fn merge_results(&mut self, results_nodes: Vec<Var>, is_cleanup: bool) {
        for node in results_nodes.iter(){
            if node.index <= self.arg_size{
                if node.alias[0] != node.local || node.alias.len() > 1 {
                    for alias in node.alias.clone(){
                        if results_nodes[alias].index <= self.arg_size
                        && !self.return_set.contains(&(node.local, alias))
                        && alias != node.local
                        && node.index != results_nodes[alias].index {
                            self.return_set.insert((node.local, alias));
                            let left_node = node;
                            let right_node = &results_nodes[alias];
                            let mut new_assign = ReturnAssign::new(0, 
                                left_node.index, left_node.may_drop, left_node.need_drop,
                                right_node.index, right_node.may_drop, right_node.need_drop
			    );
                            new_assign.left = left_node.field_info.clone();
                            new_assign.right = right_node.field_info.clone();
                            self.return_results.assignments.push(new_assign);
                        }
                    }
                }
                if node.is_ptr() && is_cleanup == false && node.is_alive() == false && node.local <= self.arg_size {
                    self.return_results.dead.insert(node.local);
                }
            }
        }
    }
}

