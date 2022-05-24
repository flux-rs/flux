use std::{collections::HashMap, iter};

use itertools::Itertools;
use rustc_span::Symbol;

use liquid_rust_syntax::surface::{Arg, FnSig, Ident, Path, RefKind, Res, Ty, TyKind};

type Locs = HashMap<Symbol, Ty<Res>>;

/// `zip_bare_def(b_sig, d_sig)` combines the refinements of the `b_sig` and the resolved elements
/// of the (trivial/default) `dsig:DefFnSig` to compute a (refined) `DefFnSig`
pub fn zip_bare_def(b_sig: FnSig, d_sig: FnSig<Res>) -> FnSig<Res> {
    let mut locs: Locs = HashMap::new();
    let default_args = d_sig.args.into_iter().map(|arg| arg.assert_ty()).collect();
    FnSig {
        args: zip_args(b_sig.args, default_args, &mut locs),
        returns: zip_ty(b_sig.returns, &d_sig.returns),
        ensures: zip_ty_locs(b_sig.ensures, &locs),
        requires: b_sig.requires,
        span: b_sig.span,
    }
}

/// `zip_ty_locs` traverses the bare-outputs and zips with the location-types saved in `locs`
fn zip_ty_locs(bindings: Vec<(Ident, Ty)>, locs: &Locs) -> Vec<(Ident, Ty<Res>)> {
    let mut res = vec![];
    for (ident, ty) in bindings {
        if let Some(default) = locs.get(&ident.name) {
            let dt = zip_ty(ty, default);
            res.push((ident, dt))
        } else {
            panic!("missing location type for `{}`", ident)
        }
    }
    res
}

/// `zip_ty_binds` traverses the inputs `bs` and `ds` and
/// saves the types of the references in `locs`
fn zip_args(binds: Vec<Arg>, defaults: Vec<Ty<Res>>, locs: &mut Locs) -> Vec<Arg<Res>> {
    if binds.len() != defaults.len() {
        panic!("bind count mismatch, expected: {:?},  found: {:?}", binds.len(), defaults.len());
    }
    let binds = iter::zip(binds, &defaults)
        .map(|(arg, default)| zip_arg(arg, default))
        .collect_vec();
    for (arg, default) in iter::zip(&binds, defaults) {
        if let (Arg::StrgRef(bind, _), TyKind::Ref(RefKind::Mut, default)) = (arg, default.kind) {
            locs.insert(bind.name, *default);
        }
    }
    binds
}

fn zip_arg(arg: Arg, default: &Ty<Res>) -> Arg<Res> {
    match (arg, &default.kind) {
        (Arg::Ty(ty), _) => Arg::Ty(zip_ty(ty, default)),
        (Arg::Indexed(bind, path, pred), TyKind::Path(default)) => {
            Arg::Indexed(bind, zip_path(path, default), pred)
        }
        (Arg::StrgRef(bind, ty), TyKind::Ref(RefKind::Mut, default)) => {
            Arg::StrgRef(bind, zip_ty(ty, default))
        }
        _ => panic!("incompatible types `{default:?}`"),
    }
}

fn zip_ty(ty: Ty, default: &Ty<Res>) -> Ty<Res> {
    let kind = match (ty.kind, &default.kind) {
        (TyKind::Path(path), TyKind::Path(default)) => TyKind::Path(zip_path(path, default)),
        (TyKind::Indexed { path, indices }, TyKind::Path(default)) => {
            TyKind::Indexed { path: zip_path(path, default), indices }
        }
        (TyKind::Exists { bind, path, pred }, TyKind::Path(default)) => {
            TyKind::Exists { bind, path: zip_path(path, default), pred }
        }
        (TyKind::StrgRef(loc, ty), TyKind::Ref(RefKind::Mut, default)) => {
            TyKind::StrgRef(loc, Box::new(zip_ty(*ty, default)))
        }
        (TyKind::Ref(rk, ty), TyKind::Ref(default_rk, default)) if rk == *default_rk => {
            TyKind::Ref(rk, Box::new(zip_ty(*ty, default)))
        }
        (TyKind::Unit, TyKind::Unit) => TyKind::Unit,
        _ => panic!("incompatible types `{default:?}`"),
    };
    Ty { kind, span: ty.span }
}

fn zip_path(path: Path, default: &Path<Res>) -> Path<Res> {
    if path.args.len() != default.args.len() {
        panic!(
            "argument count mismatch, expected: {:?},  found: {:?}",
            default.args.len(),
            path.args.len()
        );
    }
    let args = iter::zip(path.args, &default.args)
        .map(|(ty, default)| zip_ty(ty, default))
        .collect();

    Path { ident: default.ident, args, span: path.span }
}
