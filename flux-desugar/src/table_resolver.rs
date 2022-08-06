use flux_common::iter::IterExt;
use hir::{def_id::DefId, ItemId, ItemKind};
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::{self as hir, def_id::LocalDefId};
use rustc_middle::ty::{ParamTy, TyCtxt};
use rustc_session::Session;
use rustc_span::Symbol;

use flux_syntax::surface::{self, Ident, Path, Res, Ty};

pub struct Resolver<'tcx> {
    sess: &'tcx Session,
    table: NameResTable,
}

struct NameResTable {
    res: FxHashMap<Symbol, hir::def::Res>,
    generics: FxHashMap<DefId, ParamTy>,
}

impl<'tcx> Resolver<'tcx> {
    #[allow(dead_code)]

    pub fn from_fn(
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
    ) -> Result<Resolver<'tcx>, ErrorGuaranteed> {
        let mut table = init_table(tcx, def_id)?;

        let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
        table.collect_from_fn_sig(tcx.sess, tcx.hir().fn_sig_by_hir_id(hir_id).unwrap())?;

        Ok(Resolver { sess: tcx.sess, table })
    }

    pub fn from_adt(
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
    ) -> Result<Resolver<'tcx>, ErrorGuaranteed> {
        let item = tcx.hir().expect_item(def_id);

        match &item.kind {
            ItemKind::Struct(data, generics) => {
                let mut table = NameResTable::new();
                table.insert_generics(tcx, generics);

                for field in data.fields() {
                    table.collect_from_ty(tcx.sess, field.ty)?;
                }

                Ok(Resolver { sess: tcx.sess, table })
            }
            ItemKind::Enum(enum_def, generics) => {
                let mut table = NameResTable::new();
                table.insert_generics(tcx, generics);

                for variant in enum_def.variants {
                    for field in variant.data.fields() {
                        table.collect_from_ty(tcx.sess, field.ty)?;
                    }
                }
                Ok(Resolver { sess: tcx.sess, table })
            }
            _ => panic!("expected a struct or enum"),
        }
    }

    pub fn resolve_enum_def(
        &mut self,
        enum_def: surface::EnumDef,
    ) -> Result<surface::EnumDef<Res>, ErrorGuaranteed> {
        HEREHEREHEREHERE todo!()
    }

    pub fn resolve_struct_def(
        &mut self,
        struct_def: surface::StructDef,
    ) -> Result<surface::StructDef<Res>, ErrorGuaranteed> {
        let fields = struct_def
            .fields
            .into_iter()
            .map(|ty| ty.map(|ty| self.resolve_ty(ty)).transpose())
            .try_collect_exhaust()?;

        Ok(surface::StructDef {
            def_id: struct_def.def_id,
            refined_by: struct_def.refined_by,
            fields,
            opaque: struct_def.opaque,
        })
    }

    #[allow(dead_code)]
    pub fn resolve_fn_sig(
        &mut self,
        fn_sig: surface::FnSig,
    ) -> Result<surface::FnSig<Res>, ErrorGuaranteed> {
        let args = fn_sig
            .args
            .into_iter()
            .map(|arg| self.resolve_arg(arg))
            .try_collect_exhaust();

        let ensures = fn_sig
            .ensures
            .into_iter()
            .map(|(loc, ty)| Ok((loc, self.resolve_ty(ty)?)))
            .try_collect_exhaust();

        let returns = self.resolve_ty(fn_sig.returns);

        Ok(surface::FnSig {
            requires: fn_sig.requires,
            args: args?,
            returns: returns?,
            ensures: ensures?,
            span: fn_sig.span,
        })
    }

    fn resolve_arg(&self, arg: surface::Arg) -> Result<surface::Arg<Res>, ErrorGuaranteed> {
        match arg {
            surface::Arg::Indexed(bind, path, pred) => {
                Ok(surface::Arg::Indexed(bind, self.resolve_path(path)?, pred))
            }
            surface::Arg::StrgRef(loc, ty) => Ok(surface::Arg::StrgRef(loc, self.resolve_ty(ty)?)),
            surface::Arg::Ty(ty) => Ok(surface::Arg::Ty(self.resolve_ty(ty)?)),
            surface::Arg::Alias(_, _, _) => panic!("Unexpected 'Alias' in resolve_arg"),
        }
    }

    fn resolve_ty(&self, ty: Ty) -> Result<Ty<Res>, ErrorGuaranteed> {
        let kind = match ty.kind {
            surface::TyKind::Path(path) => surface::TyKind::Path(self.resolve_path(path)?),
            surface::TyKind::Indexed { path, indices } => {
                let path = self.resolve_path(path)?;
                surface::TyKind::Indexed { path, indices }
            }
            surface::TyKind::Exists { bind, path, pred } => {
                let path = self.resolve_path(path)?;
                surface::TyKind::Exists { bind, path, pred }
            }
            surface::TyKind::StrgRef(loc, ty) => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::StrgRef(loc, Box::new(ty))
            }
            surface::TyKind::Ref(rk, ty) => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::Ref(rk, Box::new(ty))
            }
            surface::TyKind::Unit => surface::TyKind::Unit,
            surface::TyKind::Constr(pred, ty) => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::Constr(pred, Box::new(ty))
            }
        };
        Ok(surface::Ty { kind, span: ty.span })
    }

    fn resolve_path(&self, path: Path) -> Result<Path<Res>, ErrorGuaranteed> {
        let ident = self.resolve_ident(path.ident)?;
        let args = path
            .args
            .into_iter()
            .map(|ty| self.resolve_ty(ty))
            .try_collect_exhaust()?;
        Ok(Path { ident, args, span: path.span })
    }

    fn resolve_ident(&self, ident: Ident) -> Result<Res, ErrorGuaranteed> {
        let res = if let Some(res) = self.table.get(ident.name) {
            *res
        } else {
            return Err(self.sess.emit_err(errors::UnresolvedPath::new(ident)));
        };

        match res {
            hir::def::Res::Def(hir::def::DefKind::TyParam, did) => {
                Ok(Res::Param(self.table.get_param_ty(did).unwrap()))
            }
            hir::def::Res::Def(hir::def::DefKind::Struct, did) => Ok(Res::Adt(did)),
            hir::def::Res::PrimTy(hir::PrimTy::Int(int_ty)) => {
                Ok(Res::Int(rustc_middle::ty::int_ty(int_ty)))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Uint(uint_ty)) => {
                Ok(Res::Uint(rustc_middle::ty::uint_ty(uint_ty)))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Bool) => Ok(Res::Bool),
            hir::def::Res::PrimTy(hir::PrimTy::Float(float_ty)) => {
                Ok(Res::Float(rustc_middle::ty::float_ty(float_ty)))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Str) => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span: ident.span,
                    msg: "string slices are not supported yet",
                }))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Char) => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span: ident.span,
                    msg: "chars are not suported yet",
                }))
            }
            hir::def::Res::Def(_, _) | hir::def::Res::SelfTy { .. } => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span: ident.span,
                    msg: "path resolved to an unsupported type",
                }))
            }
            _ => unreachable!("unexpected type resolution"),
        }
    }
}

fn init_table(tcx: TyCtxt, def_id: LocalDefId) -> Result<NameResTable, ErrorGuaranteed> {
    let mut table = NameResTable::new();
    if let Some(impl_did) = tcx.impl_of_method(def_id.to_def_id()) {
        let item_id = ItemId { def_id: impl_did.expect_local() };
        let item = tcx.hir().item(item_id);
        if let ItemKind::Impl(parent) = &item.kind {
            table.collect_from_ty(tcx.sess, parent.self_ty)?;
            table.insert_generics(tcx, parent.generics);
        }
    }

    if let Some(generics) = tcx.hir().get_generics(def_id) {
        table.insert_generics(tcx, generics);
    }
    Ok(table)
}

impl NameResTable {
    fn new() -> NameResTable {
        NameResTable { res: FxHashMap::default(), generics: FxHashMap::default() }
    }

    fn get(&self, sym: Symbol) -> Option<&hir::def::Res> {
        self.res.get(&sym)
    }

    fn get_param_ty(&self, def_id: DefId) -> Option<ParamTy> {
        self.generics.get(&def_id).copied()
    }

    fn insert_generics(&mut self, tcx: TyCtxt, generics: &hir::Generics) {
        for param in generics.params {
            if let hir::GenericParamKind::Type { .. } = param.kind {
                let def_id = tcx.hir().local_def_id(param.hir_id).to_def_id();
                assert!(!self.generics.contains_key(&def_id));

                let name = param.name.ident().name;
                let index = self.generics.len() as u32;
                let param_ty = ParamTy { index, name };
                self.generics.insert(def_id, param_ty);
            }
        }
    }

    fn collect_from_fn_sig(
        &mut self,
        sess: &Session,
        fn_sig: &hir::FnSig,
    ) -> Result<(), ErrorGuaranteed> {
        fn_sig
            .decl
            .inputs
            .iter()
            .try_for_each_exhaust(|ty| self.collect_from_ty(sess, ty))?;

        match fn_sig.decl.output {
            hir::FnRetTy::DefaultReturn(span) => {
                return Err(sess.emit_err(errors::UnsupportedSignature {
                    span,
                    msg: "default return types are not supported yet",
                }));
            }
            hir::FnRetTy::Return(ty) => {
                self.collect_from_ty(sess, ty)?;
            }
        }

        Ok(())
    }

    fn collect_from_ty(&mut self, sess: &Session, ty: &hir::Ty) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => self.collect_from_ty(sess, ty),
            hir::TyKind::Ptr(mut_ty) | hir::TyKind::Rptr(_, mut_ty) => {
                self.collect_from_ty(sess, mut_ty.ty)
            }
            hir::TyKind::Tup(tys) => tys.iter().try_for_each(|ty| self.collect_from_ty(sess, ty)),
            hir::TyKind::Path(qpath) => {
                let path = if let hir::QPath::Resolved(None, path) = qpath {
                    path
                } else {
                    return Err(sess.emit_err(errors::UnsupportedSignature {
                        span: qpath.span(),
                        msg: "unsupported type",
                    }));
                };

                let (ident, args) = match path.segments {
                    [hir::PathSegment { ident, args, .. }] => (ident, args),
                    _ => {
                        return Err(sess.emit_err(errors::UnsupportedSignature {
                            span: qpath.span(),
                            msg: "multi-segment paths are not supported yet",
                        }));
                    }
                };
                self.res.insert(ident.name, path.res);

                args.map(|args| args.args)
                    .iter()
                    .copied()
                    .flatten()
                    .try_for_each_exhaust(|arg| self.collect_from_generic_arg(sess, arg))
            }
            hir::TyKind::BareFn(_)
            | hir::TyKind::Never
            | hir::TyKind::OpaqueDef(_, _)
            | hir::TyKind::TraitObject(_, _, _)
            | hir::TyKind::Typeof(_)
            | hir::TyKind::Infer
            | hir::TyKind::Err => Ok(()),
        }
    }

    fn collect_from_generic_arg(
        &mut self,
        sess: &Session,
        arg: &hir::GenericArg,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            hir::GenericArg::Type(ty) => self.collect_from_ty(sess, ty),
            hir::GenericArg::Lifetime(_) => {
                Err(sess.emit_err(errors::UnsupportedSignature {
                    span: arg.span(),
                    msg: "lifetime parameters are not supported yet",
                }))
            }
            hir::GenericArg::Const(_) => {
                Err(sess.emit_err(errors::UnsupportedSignature {
                    span: arg.span(),
                    msg: "const generics are not supported yet",
                }))
            }

            hir::GenericArg::Infer(_) => unreachable!(),
        }
    }
}

mod errors {
    use flux_macros::SessionDiagnostic;
    use flux_syntax::surface;
    use rustc_span::{symbol::Ident, Span};

    #[derive(SessionDiagnostic)]
    #[error(resolver::unsupported_signature, code = "FLUX")]
    pub struct UnsupportedSignature {
        #[primary_span]
        #[label]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(SessionDiagnostic)]
    #[error(resolver::unresolved_path, code = "FLUX")]
    pub struct UnresolvedPath {
        #[primary_span]
        #[label]
        pub span: Span,
        pub path: Ident,
    }

    impl UnresolvedPath {
        pub fn new(ident: surface::Ident) -> Self {
            Self { span: ident.span, path: ident }
        }
    }
}
