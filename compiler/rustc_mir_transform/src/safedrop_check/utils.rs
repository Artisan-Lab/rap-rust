use rustc_middle::ty::TyCtxt;
use rustc_middle::mir::{Local, LocalDecl};
use rustc_span::symbol::Symbol;

/// Extract the variable name using `Local` and `LocalDecl`.
pub fn get_var_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    local: Local,
    local_decl: &LocalDecl<'tcx>,
) -> Option<Symbol> {
    // Skip the return place or other unnamed locals
    if local.index() == 0 {
        return None;
    }

    let span = local_decl.source_info.span;
    let name = tcx.sess.source_map().span_to_snippet(span).ok()?;
    //println!("{:?}",Some(Symbol::intern(&name)));
    Some(Symbol::intern(&name))
}

