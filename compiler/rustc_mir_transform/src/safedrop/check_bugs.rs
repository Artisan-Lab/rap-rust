use rustc_middle::mir::SourceInfo;
use rustc_span::Span;
use rustc_span::symbol::Symbol;
use rustc_data_structures::fx::FxHashSet;
use super::graph::*;
use super::utils::*;
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


    pub fn uaf_check(&mut self, used: usize, span: Span, origin: usize, is_func_call: bool) {
        let mut record = FxHashSet::default();
        if self.values[used].may_drop && (!self.values[used].is_ptr() || self.values[used].index != origin || is_func_call)
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
                    if self.values[i+1].is_ptr() && self.is_dangling(i+1) {
                        self.bug_records.dp_bugs_unwind.insert(self.span);
                    }
                }
            },
            false => { 
                if self.values[0].may_drop && self.is_dangling(0){
                    self.bug_records.dp_bugs.insert(self.span);
                } else{
                    for i in 0..self.arg_size {
                        if self.values[i+1].is_ptr() && self.is_dangling(i+1) {
                            self.bug_records.dp_bugs.insert(self.span);
                        }
                    }
                }
            },
        }
    }

    pub fn dead_node(&mut self, drop: usize, life_begin: usize, info: &SourceInfo, alias: bool) {
        //Rc drop
        if self.values[drop].is_corner_case() {
            return;
        } 
        //check if there is a double free bug.
        if self.df_check(drop, info.span) {
            return;
        }
        //drop their alias
        if self.values[drop].alias[0] != drop {
            for i in self.values[drop].alias.clone().into_iter() {
                if self.values[i].is_ref(){
                    continue;
                }
                self.dead_node(i, life_begin, info, true);
            }
        }
        //drop the fields of the root node.
        //alias flag is used to avoid the fields of the alias are dropped repeatly.
        if alias == false {
            for i in self.values[drop].fields.clone().into_iter() {
                if self.values[drop].is_tuple() == true && self.values[i.1].need_drop == false {
                    continue;
                } 
                self.dead_node( i.1, life_begin, info, false);
            }
        }
        //SCC.
        if self.values[drop].alive < life_begin as isize && self.values[drop].may_drop {
            self.values[drop].dead();   
        }
    }
    //merge the result of current path to the final result.
    pub fn merge_results(&mut self, results_nodes: Vec<ValueNode>, is_cleanup: bool) {
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
                            let mut new_assign = RetAssign::new(0, 
                                left_node.index, left_node.may_drop, left_node.need_drop,
                                right_node.index, right_node.may_drop, right_node.need_drop
			    );
                            new_assign.left = left_node.field_info.clone();
                            new_assign.right = right_node.field_info.clone();
                            self.ret_results.assignments.push(new_assign);
                        }
                    }
                }
                if node.is_ptr() && is_cleanup == false && node.is_alive() == false && node.local <= self.arg_size {
                    self.ret_results.dead.insert(node.local);
                }
            }
        }
    }
}


