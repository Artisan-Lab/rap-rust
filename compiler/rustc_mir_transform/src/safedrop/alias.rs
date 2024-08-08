use crate::rap_error;
use rustc_data_structures::fx::FxHashSet;
use super::graph::*;
use super::log::*;
use log::Log;

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
