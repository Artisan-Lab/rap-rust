use rustc_middle::ty::TyCtxt;
use rustc_middle::mir::{Local, LocalDecl};
use rustc_span::symbol::Symbol;
use rustc_span::def_id::DefId;

/// Extract the variable name using `Local` and `LocalDecl`.
pub fn get_name<'tcx>(
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

pub fn get_fn_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Symbol> {
    // Check if the DefId corresponds to a local crate
    if def_id.is_local() {
        // Use the HIR map to get the HIR item
        if let Some(item) = tcx.hir().find_by_def_id(def_id.expect_local()) {
            // Extract the name if it's an item (e.g., a function)
            if let rustc_hir::Node::Item(item) = item {
                if let rustc_hir::ItemKind::Fn(..) = item.kind {
                    return Some(item.ident.name);
                }
            }
        }
    }
    None
}
