use std::{collections::HashMap, iter};

use flux_middle::rustc::ty::{self as rustc_ty, Mutability};
use flux_syntax::surface::{Arg, FnSig, Ident, Path, RefKind, Res, Ty, TyKind};
use itertools::Itertools;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

type Locs = HashMap<Symbol, rustc_ty::Ty>;

/// `zip_bare_def(b_sig, d_sig)` combines the refinements of the `b_sig` and the resolved elements
/// of the (trivial/default) `dsig:DefFnSig` to compute a (refined) `DefFnSig`
pub fn zip_bare_def(tcx: TyCtxt, sig: FnSig, rust_sig: &rustc_ty::FnSig) -> FnSig<Res> {
    let mut locs = Locs::new();
    FnSig {
        args: zip_args(tcx, sig.args, rust_sig.inputs(), &mut locs),
        returns: zip_ty(tcx, sig.returns, &rust_sig.output()),
        ensures: zip_ty_locs(tcx, sig.ensures, &locs),
        requires: sig.requires,
        span: sig.span,
    }
}

/// `zip_ty_locs` traverses the bare-outputs and zips with the location-types saved in `locs`
fn zip_ty_locs(tcx: TyCtxt, bindings: Vec<(Ident, Ty)>, locs: &Locs) -> Vec<(Ident, Ty<Res>)> {
    let mut res = vec![];
    for (ident, ty) in bindings {
        if let Some(rust_ty) = locs.get(&ident.name) {
            let dt = zip_ty(tcx, ty, rust_ty);
            res.push((ident, dt))
        } else {
            panic!("missing location type for `{}`", ident)
        }
    }
    res
}

/// `zip_ty_binds` traverses the inputs `bs` and `ds` and
/// saves the types of the references in `locs`
fn zip_args(
    tcx: TyCtxt,
    binds: Vec<Arg>,
    rust_tys: &[rustc_ty::Ty],
    locs: &mut Locs,
) -> Vec<Arg<Res>> {
    if binds.len() != rust_tys.len() {
        panic!("bind count mismatch, expected: {:?},  found: {:?}", binds.len(), rust_tys.len());
    }
    let binds = iter::zip(binds, rust_tys)
        .map(|(arg, rust_ty)| zip_arg(tcx, arg, rust_ty))
        .collect_vec();
    for (arg, rust_ty) in iter::zip(&binds, rust_tys) {
        if let (Arg::StrgRef(bind, _), rustc_ty::TyKind::Ref(rust_ty, Mutability::Mut)) =
            (arg, rust_ty.kind())
        {
            locs.insert(bind.name, rust_ty.clone());
        }
    }
    binds
}

fn zip_arg(tcx: TyCtxt, arg: Arg, rust_ty: &rustc_ty::Ty) -> Arg<Res> {
    match (arg, rust_ty.kind()) {
        (Arg::Ty(ty), _) => Arg::Ty(zip_ty(tcx, ty, rust_ty)),
        (Arg::Indexed(bind, path, pred), _) => {
            Arg::Indexed(bind, zip_path(tcx, path, rust_ty), pred)
        }
        (Arg::StrgRef(bind, ty), rustc_ty::TyKind::Ref(rust_ty, Mutability::Mut)) => {
            Arg::StrgRef(bind, zip_ty(tcx, ty, rust_ty))
        }
        _ => panic!("incompatible types `{rust_ty:?}`"),
    }
}

fn zip_ty(tcx: TyCtxt, ty: Ty, rust_ty: &rustc_ty::Ty) -> Ty<Res> {
    let kind = match (ty.kind, rust_ty.kind()) {
        (TyKind::Path(path), _) => TyKind::Path(zip_path(tcx, path, rust_ty)),
        (TyKind::Indexed { path, indices }, _) => {
            TyKind::Indexed { path: zip_path(tcx, path, rust_ty), indices }
        }
        (TyKind::Exists { bind, path, pred }, _) => {
            TyKind::Exists { bind, path: zip_path(tcx, path, rust_ty), pred }
        }
        (TyKind::Constr(pred, ty), _) => TyKind::Constr(pred, Box::new(zip_ty(tcx, *ty, rust_ty))),
        (TyKind::StrgRef(loc, ty), rustc_ty::TyKind::Ref(rust_ty, Mutability::Mut)) => {
            TyKind::StrgRef(loc, Box::new(zip_ty(tcx, *ty, rust_ty)))
        }
        (TyKind::Ref(RefKind::Mut, ty), rustc_ty::TyKind::Ref(rust_ty, Mutability::Mut)) => {
            TyKind::Ref(RefKind::Mut, Box::new(zip_ty(tcx, *ty, rust_ty)))
        }
        (TyKind::Ref(RefKind::Shr, ty), rustc_ty::TyKind::Ref(rust_ty, Mutability::Not)) => {
            TyKind::Ref(RefKind::Shr, Box::new(zip_ty(tcx, *ty, rust_ty)))
        }
        (TyKind::Unit, rustc_ty::TyKind::Tuple(tys)) if tys.is_empty() => TyKind::Unit,

        _ => panic!("incompatible types: `{rust_ty:?}`"),
    };
    Ty { kind, span: ty.span }
}

fn zip_path(tcx: TyCtxt, path: Path, rust_ty: &rustc_ty::Ty) -> Path<Res> {
    let (res, rust_args) = rustc_ty_ident_args(rust_ty);

    let path_args_len = path.args.len();
    // Assume that the rust_args are of the form [path_args + default_args]
    // i.e. default args all come _after_ the supplied path_args.
    let rust_args_len = rust_args.len();
    let default_args_len = rust_args_len - path_args_len;
    assert!(default_args_len <= rust_args_len);

    // zip the supplied args
    let args = iter::zip(path.args, rust_args)
        .map(|(arg, rust_arg)| zip_generic_arg(tcx, arg, rust_arg))
        .collect();
    Path { ident: res, args, span: path.span }
}

fn rustc_ty_ident_args(rust_ty: &rustc_ty::Ty) -> (Res, &[rustc_ty::GenericArg]) {
    match rust_ty.kind() {
        rustc_ty::TyKind::Adt(def_id, substs) => (Res::Adt(*def_id), &substs[..]),
        rustc_ty::TyKind::Uint(uint_ty) => (Res::Uint(*uint_ty), [].as_slice()),
        rustc_ty::TyKind::Bool => (Res::Bool, [].as_slice()),
        rustc_ty::TyKind::Float(float_ty) => (Res::Float(*float_ty), [].as_slice()),
        rustc_ty::TyKind::Int(int_ty) => (Res::Int(*int_ty), [].as_slice()),
        rustc_ty::TyKind::Param(param_ty) => (Res::Param(*param_ty), [].as_slice()),
        _ => panic!("incompatible type: `{rust_ty:?}`"),
    }
}

fn zip_generic_arg(tcx: TyCtxt, arg: Ty, rust_arg: &rustc_ty::GenericArg) -> Ty<Res> {
    match rust_arg {
        rustc_ty::GenericArg::Ty(ty) => zip_ty(tcx, arg, ty),
    }
}
