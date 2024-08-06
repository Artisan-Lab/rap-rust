use rustc_middle::ty;
use rustc_middle::ty::{Ty, TyCtxt};
use super::corner_handle::is_corner_adt;

pub fn kind<'tcx>(current_ty: Ty<'tcx>) -> usize {
    match current_ty.kind() {
        ty::RawPtr(..) => 1,
        ty::Ref(..) => 4,
        ty::Tuple(..) => 2,
        ty::Adt(ref adt_def, _) => {
            if is_corner_adt(format!("{:?}", adt_def)) {
                return 3;
            }
            else{
                return 0;
            }
        },
        _ => 0,
    }
}

pub fn is_not_drop<'tcx>(tcx: TyCtxt<'tcx>, current_ty: Ty<'tcx>) -> bool {
    match current_ty.kind() {
        ty::Bool
        | ty::Char
        | ty::Int(_)
        | ty::Uint(_)
        | ty::Float(_) => true,
        ty::Array(ref tys,_) => is_not_drop(tcx, *tys),
        ty::Adt(ref adtdef, ref substs) => {
            for field in adtdef.all_fields() {
                if !is_not_drop(tcx, field.ty(tcx, substs)) {
                    return false;
                }
            }
            true
        },
        ty::Tuple(ref tuple_fields) => {
            for tys in tuple_fields.iter() {
                if !is_not_drop(tcx, tys) {
                    return false;
                }
            }
            true
        },
        _ => false,
    }
}
