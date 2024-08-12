use std::vec::Vec;
use std::cmp::min;
use rustc_middle::mir::StatementKind;
use rustc_middle::mir::TerminatorKind;
use rustc_middle::mir::Body;
use rustc_middle::mir::BasicBlock;
//use rustc_middle::mir::Local;
use rustc_middle::mir::Terminator;
use rustc_middle::mir::Place;
use rustc_middle::mir::UnwindAction;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::Operand;
use rustc_middle::mir::Rvalue;
use rustc_middle::ty;
use rustc_span::Span;
use super::safedrop::*;
use super::bug_records::*;
use super::alias::*;
use super::types::*;

#[derive(PartialEq,Debug,Clone)]
pub enum AssignType {
    Copy,
    Move,
    Field,
    Variant,
}

//self-defined assignments structure. 
#[derive(Debug,Clone)]
pub struct Assignment<'tcx>{
    pub left: Place<'tcx>,
    pub right: Place<'tcx>,
    pub atype: AssignType,
    pub span: Span,
}

impl<'tcx> Assignment<'tcx>{
    pub fn new(left: Place<'tcx>, right: Place<'tcx>, atype: AssignType, span: Span)->Assignment<'tcx>{
        Assignment{
            left: left,
            right: right,
            atype: atype,
            span: span,
        }
    }
}

/* 
 * Self-defined basicblock structure;
 * Used both for the original CFG and after SCC.
 */

#[derive(Debug,Clone)]
pub struct BlockNode<'tcx>{
    pub index: usize,
    pub is_cleanup: bool,
    pub next: FxHashSet<usize>,
    pub assignments: Vec<Assignment<'tcx>>,
    pub calls: Vec<Terminator<'tcx>>,
    pub drops: Vec<Terminator<'tcx>>,
    //store the index of the basic blocks as a SCC node. 
    pub scc_sub_blocks: Vec<usize>,
    //store the const value defined in this block;
    pub const_value: Vec::<(usize, usize)>,
    //store switch stmts in current block for the path filtering in path-sensitive analysis.
    pub switch_stmts: Vec::<Terminator<'tcx>>,
}

impl<'tcx> BlockNode<'tcx>{
    pub fn new(index:usize, is_cleanup: bool) -> BlockNode<'tcx>{
        BlockNode{
            index: index,
            is_cleanup: is_cleanup,
            next: FxHashSet::<usize>::default(),
            assignments: Vec::<Assignment<'tcx>>::new(),
            calls: Vec::<Terminator<'tcx>>::new(),
            drops: Vec::<Terminator<'tcx>>::new(),
            scc_sub_blocks: Vec::<usize>::new(),
            const_value: Vec::<(usize, usize)>::new(),
            switch_stmts: Vec::<Terminator<'tcx>>::new(),
        }
    }

    pub fn add_next(&mut self, index: usize){
        self.next.insert(index);
    }
}

#[derive(Debug,Clone)]
pub struct Var {
    pub index: usize,
    pub local: usize,
    pub need_drop: bool,
    pub may_drop: bool,
    pub kind: usize,
    pub father: usize,
    pub alias: Vec<usize>,
    pub alive: isize,
    pub sons: FxHashMap<usize, usize>,
    pub field_info: Vec<usize>,
}

impl Var {
    pub fn new(index: usize, local: usize, need_drop: bool, may_drop: bool) -> Self {
        let mut eq = Vec::new();
        eq.push(local);
        Var { index: index, local: local, need_drop: need_drop, 
              father: local, alias: eq, alive: 0, may_drop: may_drop, 
              kind: 0, sons: FxHashMap::default(), field_info: Vec::<usize>::new() }
    }

    pub fn dead(&mut self) { self.alive = -1; }

    pub fn is_alive(&self) -> bool { self.alive > -1 }

    pub fn is_tuple(&self)-> bool { self.kind == 2 }

    pub fn is_ptr(&self)-> bool {
        return self.kind == 1 || self.kind == 4;
    }

    pub fn is_ref(&self)-> bool { self.kind == 4 }

    pub fn is_corner_case(&self)-> bool { self.kind == 3 }
}

pub struct SafeDropGraph<'tcx>{
    pub def_id: DefId,
    pub tcx: TyCtxt<'tcx>,
    pub span: Span,
    // contains all varibles (including fields) as vars.
    pub vars: Vec<Var>,
    // contains all blocks in the CFG
    pub blocks: Vec<BlockNode<'tcx>>,
    pub arg_size: usize, 
    // we shrink a SCC into a node and use a scc node to represent the SCC.
    pub scc_indices: Vec<usize>,
    // record the constant value during safedrop checking.
    pub constant: FxHashMap<usize, usize>,
    // used for tarjan algorithmn.
    pub count: usize,
    // contains the return results for inter-procedure analysis.
    pub return_results: ReturnResults,
    // used for filtering duplicate alias assignments in return results.
    pub return_set: FxHashSet<(usize, usize)>,
    // record the information of bugs for the function.
    pub bug_records: BugRecords,
    // a threhold to avoid path explosion.
    pub visit_times: usize
}

impl<'tcx> SafeDropGraph<'tcx>{
    pub fn new(body: &Body<'tcx>,  tcx: TyCtxt<'tcx>, def_id: DefId) -> SafeDropGraph<'tcx>{  
        // handle variables
        let locals = &body.local_decls;
        let arg_size = body.arg_count;
        let mut vars = Vec::<Var>::new();
        let param_env = tcx.param_env(def_id);
        for (local, local_decl) in locals.iter_enumerated() {
            let need_drop = local_decl.ty.needs_drop(tcx, param_env); // the type is drop
            let may_drop = !is_not_drop(tcx, local_decl.ty);
            let mut node = Var::new(local.as_usize(), local.as_usize(), need_drop, need_drop || may_drop);
            node.kind = kind(local_decl.ty);
            vars.push(node);
        }
        
        let basicblocks = &body.basic_blocks;
        let mut blocks = Vec::<BlockNode<'tcx>>::new();
        let mut scc_indices = Vec::<usize>::new();
        
        // handle each basicblock
        for i in 0..basicblocks.len(){
            scc_indices.push(i);
            let iter = BasicBlock::from(i);
            let terminator = basicblocks[iter].terminator.clone().unwrap();
            let mut cur_bb = BlockNode::new(i, basicblocks[iter].is_cleanup);
            
            // handle general statements
            for statement in &basicblocks[iter].statements{
		        /* Assign is a tuple defined as Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>) */
                if let StatementKind::Assign(ref assign) = statement.kind {
                    let left_ssa = assign.0.local.as_usize(); // assign.0 is a Place
                    let left = assign.0.clone();
                    match assign.1 { // assign.1 is a Rvalue
                        Rvalue::Use(ref x) => {
                            match x {
                                Operand::Copy(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if vars[left_ssa].may_drop && vars[right_ssa].may_drop{
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, AssignType::Copy, statement.source_info.span.clone());
                                        cur_bb.assignments.push(assign);
                                    }
                                },
                                Operand::Move(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if vars[left_ssa].may_drop && vars[right_ssa].may_drop{
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, AssignType::Move, statement.source_info.span.clone());
                                        cur_bb.assignments.push(assign);
                                    }
                                },
                                Operand::Constant(ref constant) => { 
                                    if let None = constant.const_.try_to_scalar(){
                                        continue;
                                    }
                                    if let Err(_tmp) = constant.const_.try_to_scalar().clone().unwrap().try_to_int(){
                                        continue;
                                    }
                                    if let Some(ans) = constant.const_.try_eval_target_usize(tcx, param_env){
                                        cur_bb.const_value.push((left_ssa, ans as usize));
                                        continue;
                                    }
                                    if let Some(const_bool) = constant.const_.try_to_bool() {
                                        cur_bb.const_value.push((left_ssa, const_bool as usize));
                                    }
                                    continue;
                                },
                            }
                        }
                        Rvalue::Ref(_, _, ref p) | Rvalue::AddressOf(_, ref p) => {
                            let right_ssa = p.local.as_usize();
                            if vars[left_ssa].may_drop && vars[right_ssa].may_drop{
                                let right = p.clone();
                                let assign = Assignment::new(left, right, AssignType::Copy, statement.source_info.span.clone());
                                cur_bb.assignments.push(assign);
                            }
                        },
                        Rvalue::ShallowInitBox(ref x, _) => {
                            if vars[left_ssa].sons.contains_key(&0) == false{
                                let mut node = Var::new(left_ssa, vars.len(), false, true);
                                let mut node1 = Var::new(left_ssa, vars.len() + 1, false, true);
                                let mut node2 = Var::new(left_ssa, vars.len() + 2, false, true);
                                node.alive = vars[left_ssa].alive;
                                node1.alive = node.alive;
                                node2.alive = node.alive;
                                node.sons.insert(0, node1.local);
                                node.field_info.push(0);
                                node1.sons.insert(0, node2.local);
                                node1.field_info.push(0);
                                node1.field_info.push(0);
                                node2.field_info.push(0);
                                node2.field_info.push(0);
                                node2.field_info.push(0);
                                node2.kind = 1;
                                vars[left_ssa].sons.insert(0, node.local);
                                vars.push(node);
                                vars.push(node1);
                                vars.push(node2);
                            }
                            match x {
                                Operand::Copy(ref p) | Operand::Move(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if vars[left_ssa].may_drop && vars[right_ssa].may_drop{
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, AssignType::Field, statement.source_info.span.clone());
                                        cur_bb.assignments.push(assign);
                                    }
                                },
                                Operand::Constant(_) => {},
                            }
                        },
                        Rvalue::Cast(_, ref x, _) => {
                            match x {
                                Operand::Copy(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if vars[left_ssa].may_drop && vars[right_ssa].may_drop{
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, AssignType::Copy, statement.source_info.span.clone());
                                        cur_bb.assignments.push(assign);
                                    }
                                },
                                Operand::Move(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if vars[left_ssa].may_drop && vars[right_ssa].may_drop{
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, AssignType::Move, statement.source_info.span.clone());
                                        cur_bb.assignments.push(assign);
                                    }
                                },
                                Operand::Constant(_) => {},
                            }
                        },
                        Rvalue::Aggregate(_, ref x) => {
                            for each_x in x {
                                match each_x {
                                    Operand::Copy(ref p) | Operand::Move(ref p) => {
                                        let right_ssa = p.local.as_usize();
                                        if vars[left_ssa].may_drop && vars[right_ssa].may_drop{
                                            let right = p.clone();
                                            let assign = Assignment::new(left, right, AssignType::Copy, statement.source_info.span.clone());
                                            cur_bb.assignments.push(assign);
                                        }
                                    },
                                    Operand::Constant(_) => {},
                                }
                            }
                        },
                        Rvalue::Discriminant(ref p) => {
                            let right = p.clone();
                            let assign = Assignment::new(left, right, AssignType::Variant, statement.source_info.span.clone());
                            cur_bb.assignments.push(assign);
                        }
                        _ => {}
                    }
                }
            }

            // handle terminator statements
            match terminator.kind {
                TerminatorKind::Goto { ref target } => {
                    cur_bb.add_next(target.as_usize());
                },
                TerminatorKind::SwitchInt{ discr: _, ref targets } => {
                    cur_bb.switch_stmts.push(terminator.clone());
                    for (_, ref target) in targets.iter() {
                        cur_bb.add_next(target.as_usize());
                    }
                    cur_bb.add_next(targets.otherwise().as_usize());
                }, 
                TerminatorKind::UnwindResume => {},
                TerminatorKind::Return => {},
                TerminatorKind::UnwindTerminate(_)
                | TerminatorKind::GeneratorDrop
                | TerminatorKind::Unreachable => {}
                TerminatorKind::Drop { place: _, ref target, ref unwind , replace: _} => {
                    cur_bb.add_next(target.as_usize());
                    cur_bb.drops.push(terminator.clone());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                },
                TerminatorKind::Call { ref func, args: _, destination: _, ref target, ref unwind, call_source: _, fn_span: _ } => {
                    match func {
                        Operand::Constant(c) => {
                            match c.ty().kind() {
                                ty::FnDef(id, ..) => {
                                    // Fixme: std::mem::drop = 1634, std::ptr::drop_in_place = 2160
                                    if id.index.as_usize() == DROP || id.index.as_usize() == DROP_IN_PLACE {
                                        cur_bb.drops.push(terminator.clone());
                                    }
                                }
                                _ => {}
                            }
                        }
                        _ => (),
                    }

                    if let Some(tt) = target {
                        cur_bb.add_next(tt.as_usize());
                    }
                    if let UnwindAction::Cleanup(tt) = unwind {
                        cur_bb.add_next(tt.as_usize());
                    }
                    cur_bb.calls.push(terminator.clone());
                },
                TerminatorKind::Assert { cond: _, expected: _, msg: _, ref target, ref unwind } => {
                    cur_bb.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                },
                TerminatorKind::Yield { value: _, ref resume, resume_arg: _, ref drop } => {
                    cur_bb.add_next(resume.as_usize());
                    if let Some(target) = drop {
                        cur_bb.add_next(target.as_usize());
                    }
                },
                TerminatorKind::FalseEdge { ref real_target, imaginary_target: _ } => {
                    cur_bb.add_next(real_target.as_usize());
                },
                TerminatorKind::FalseUnwind { ref real_target, unwind: _ } => {
                    cur_bb.add_next(real_target.as_usize());
                },
                TerminatorKind::InlineAsm { template: _, operands: _, options: _, line_spans: _, ref destination, ref unwind} => {
                    if let Some(target) = destination {
                        cur_bb.add_next(target.as_usize());
                    }
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                }
            }
            blocks.push(cur_bb);
        }

        SafeDropGraph{
            def_id: def_id.clone(),
            tcx: tcx,
            span: body.span,
            blocks: blocks,
            vars: vars,
            arg_size: arg_size,
            scc_indices: scc_indices,
            constant: FxHashMap::default(), 
            count: 0,
            return_results: ReturnResults::new(arg_size),
            return_set: FxHashSet::default(),
            bug_records: BugRecords::new(),
            visit_times: 0,
        }
    }

    pub fn tarjan(&mut self, index: usize, stack: &mut Vec<usize>, instack: &mut FxHashSet<usize>,
                  dfn: &mut Vec<usize>, low: &mut Vec<usize>) {
        dfn[index] = self.count;
        low[index] = self.count;
        self.count += 1;
        instack.insert(index);
        stack.push(index);
        let out_set = self.blocks[index].next.clone();    
        for i in out_set{
            let target = i;
            if dfn[target] == 0{
                self.tarjan(target, stack, instack, dfn, low);
                low[index] = min(low[index], low[target]);
            }
            else{
                if instack.contains(&target){
                    low[index] = min(low[index], dfn[target]);
                }
            }
        }
        // generate SCC
        if dfn[index] == low[index] {
            loop {
                let node = stack.pop().unwrap();
                self.scc_indices[node] = index;
                instack.remove(&node);
                if index == node { // we have found all nodes of the current scc.
                    break;
                }
                self.blocks[index].scc_sub_blocks.push(node);
                let nexts = self.blocks[node].next.clone();
                for i in nexts {
                    self.blocks[index].next.insert(i);
                }
            } 
            /* remove next nodes which are already in the current SCC */
            let mut to_remove = Vec::new();
            for i in self.blocks[index].next.iter() {
                if self.scc_indices[*i] == index {
                    to_remove.push(*i);
                }
            }
            for i in to_remove {
                self.blocks[index].next.remove(&i);
            }
            /* To ensure a resonable order of blocks within one SCC, 
             * so that the scc can be directly used for followup analysis without referencing the
             * original graph.
             * */
            self.blocks[index].scc_sub_blocks.reverse();
        }
    }

    // handle SCC
    pub fn solve_scc(&mut self) {
        let mut stack = Vec::<usize>::new();
        let mut instack = FxHashSet::<usize>::default();
        let mut dfn = vec![0 as usize; self.blocks.len()];
        let mut low = vec![0 as usize; self.blocks.len()];
        self.tarjan(0, &mut stack, &mut instack, &mut dfn, &mut low);
    }
}
