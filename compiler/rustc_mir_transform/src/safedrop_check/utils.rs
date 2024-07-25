use rustc_middle::ty::TyCtxt;
use rustc_middle::mir::LocalDecl;
use rustc_span::symbol::Symbol;
use rustc_span::def_id::DefId;
use rustc_span::{FileName, FileNameDisplayPreference};

/// Extract the variable name using `Local` and `LocalDecl`.
pub fn get_name<'tcx>(tcx: TyCtxt<'tcx>, local_decl: &LocalDecl<'tcx>) -> Option<Symbol> {
    let span = local_decl.source_info.span;
    let name = tcx.sess.source_map().span_to_snippet(span).ok()?;
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

pub fn get_filename(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    // Get the HIR node corresponding to the DefId
    if let Some(local_id) = def_id.as_local() {
	let hir_id = tcx.hir().local_def_id_to_hir_id(local_id);
        let span = tcx.hir().span(hir_id);
        let source_map = tcx.sess.source_map();

        // Retrieve the file name
        if let Some(filename) = source_map.span_to_filename(span).into() {
            return Some(convert_filename(filename));
        }
    }

    None
}

fn convert_filename(filename: FileName) -> String {
    match filename {
        FileName::Real(path) => path.to_string_lossy(FileNameDisplayPreference::Local).into_owned(),
        _ => "<unknown>".to_string(),
    }
}
