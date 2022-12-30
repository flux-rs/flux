use flux_common::iter::IterExt;
use flux_errors::FluxSession;
use flux_syntax::surface::{self, BaseTy, Ident, Path, Res, Ty};
use hir::{def_id::DefId, ItemKind};
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::{self as hir, def_id::LocalDefId};
use rustc_middle::ty::{ParamTy, TyCtxt, TyKind};
use rustc_span::{Span, Symbol};

pub struct Resolver<'genv, 'tcx> {
    sess: &'genv FluxSession,
    table: NameResTable<'genv, 'tcx>,
}

struct NameResTable<'sess, 'tcx> {
    res: FxHashMap<Symbol, Res>,
    generics: FxHashMap<DefId, ParamTy>,
    sess: &'sess FluxSession,
    tcx: TyCtxt<'tcx>,
}

impl<'sess, 'tcx> Resolver<'sess, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        def_id: LocalDefId,
    ) -> Result<Self, ErrorGuaranteed> {
        let table = match tcx.def_kind(def_id) {
            hir::def::DefKind::Struct | hir::def::DefKind::Enum | hir::def::DefKind::Fn => {
                NameResTable::from_item(tcx, sess, def_id)?
            }
            hir::def::DefKind::AssocFn => NameResTable::from_impl_item(tcx, sess, def_id)?,
            kind => panic!("unsupported kind {kind:?}"),
        };

        Ok(Self { sess, table })
    }

    pub fn resolve_enum_def(
        &self,
        enum_def: surface::EnumDef,
    ) -> Result<surface::EnumDef<Res>, ErrorGuaranteed> {
        let variants = enum_def
            .variants
            .into_iter()
            .map(|variant| self.resolve_variant(variant))
            .try_collect_exhaust()?;

        Ok(surface::EnumDef {
            def_id: enum_def.def_id,
            refined_by: enum_def.refined_by,
            invariants: enum_def.invariants,
            variants,
        })
    }

    fn resolve_variant(
        &self,
        variant: surface::VariantDef,
    ) -> Result<surface::VariantDef<Res>, ErrorGuaranteed> {
        let fields = variant
            .fields
            .into_iter()
            .map(|ty| self.resolve_ty(ty))
            .try_collect_exhaust()?;
        let ret = self.resolve_variant_ret(variant.ret)?;
        Ok(surface::VariantDef { fields, ret, span: variant.span })
    }

    fn resolve_variant_ret(
        &self,
        ret: surface::VariantRet,
    ) -> Result<surface::VariantRet<Res>, ErrorGuaranteed> {
        let path = self.resolve_path(ret.path)?;
        Ok(surface::VariantRet { path, indices: ret.indices })
    }

    pub fn resolve_struct_def(
        &self,
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
            invariants: struct_def.invariants,
        })
    }

    #[allow(dead_code)]
    pub fn resolve_fn_sig(
        &self,
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

        let returns = fn_sig.returns.map(|ty| self.resolve_ty(ty)).transpose();

        Ok(surface::FnSig {
            params: fn_sig.params,
            requires: fn_sig.requires,
            args: args?,
            returns: returns?,
            ensures: ensures?,
            span: fn_sig.span,
        })
    }

    fn resolve_arg(&self, arg: surface::Arg) -> Result<surface::Arg<Res>, ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, pred) => {
                Ok(surface::Arg::Constr(bind, self.resolve_path(path)?, pred))
            }
            surface::Arg::StrgRef(loc, ty) => Ok(surface::Arg::StrgRef(loc, self.resolve_ty(ty)?)),
            surface::Arg::Ty(bind, ty) => Ok(surface::Arg::Ty(bind, self.resolve_ty(ty)?)),
            surface::Arg::Alias(_, _, _) => panic!("Unexpected 'Alias' in resolve_arg"),
        }
    }

    fn resolve_ty(&self, ty: Ty) -> Result<Ty<Res>, ErrorGuaranteed> {
        let kind = match ty.kind {
            surface::TyKind::Base(bty) => surface::TyKind::Base(self.resolve_bty(bty)?),
            surface::TyKind::Indexed { bty, indices } => {
                let bty = self.resolve_bty(bty)?;
                surface::TyKind::Indexed { bty, indices }
            }
            surface::TyKind::Exists { bind, bty, pred } => {
                let bty = self.resolve_bty(bty)?;
                surface::TyKind::Exists { bind, bty, pred }
            }
            surface::TyKind::Ref(rk, ty) => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::Ref(rk, Box::new(ty))
            }
            surface::TyKind::Constr(pred, ty) => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::Constr(pred, Box::new(ty))
            }

            surface::TyKind::Tuple(tys) => {
                let tys = tys
                    .into_iter()
                    .map(|ty| self.resolve_ty(ty))
                    .try_collect_exhaust()?;
                surface::TyKind::Tuple(tys)
            }
            surface::TyKind::Array(ty, len) => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::Array(Box::new(ty), len)
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

    fn resolve_bty(&self, bty: BaseTy) -> Result<BaseTy<Res>, ErrorGuaranteed> {
        match bty {
            BaseTy::Path(path) => Ok(BaseTy::Path(self.resolve_path(path)?)),

            BaseTy::Slice(ty) => {
                let ty = self.resolve_ty(*ty)?;
                Ok(BaseTy::Slice(Box::new(ty)))
            }
        }
    }

    pub fn resolve_ident(&self, ident: Ident) -> Result<Res, ErrorGuaranteed> {
        if let Some(res) = self.table.get(ident.name) {
            Ok(*res)
        } else {
            Err(self.sess.emit_err(errors::UnresolvedPath::new(ident)))
        }
    }
}

impl<'sess, 'tcx> NameResTable<'sess, 'tcx> {
    fn from_item(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        def_id: LocalDefId,
    ) -> Result<Self, ErrorGuaranteed> {
        let item = tcx.hir().expect_item(def_id);
        let mut table = Self::new(tcx, sess);
        match &item.kind {
            ItemKind::Struct(data, generics) => {
                table.insert_generics(tcx, generics);
                table
                    .res
                    .insert(item.ident.name, Res::Adt(def_id.to_def_id()));

                for field in data.fields() {
                    table.collect_from_ty(field.ty)?;
                }
            }
            ItemKind::Enum(data, generics) => {
                table.insert_generics(tcx, generics);
                table
                    .res
                    .insert(item.ident.name, Res::Adt(def_id.to_def_id()));

                for variant in data.variants {
                    for field in variant.data.fields() {
                        table.collect_from_ty(field.ty)?;
                    }
                }
            }
            ItemKind::Fn(fn_sig, generics, _) => {
                table.insert_generics(tcx, generics);
                table.collect_from_fn_sig(fn_sig)?;
            }
            _ => {}
        }
        Ok(table)
    }

    fn from_impl_item(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        def_id: LocalDefId,
    ) -> Result<Self, ErrorGuaranteed> {
        let impl_item = tcx.hir().expect_impl_item(def_id);

        let mut table = Self::new(tcx, sess);

        // Insert generics from parent impl
        if let Some(parent_impl_did) = tcx.impl_of_method(def_id.to_def_id()) {
            let parent_impl_item = tcx.hir().expect_item(parent_impl_did.expect_local());
            if let ItemKind::Impl(parent) = &parent_impl_item.kind {
                table.insert_generics(tcx, parent.generics);
                table.collect_from_ty(parent.self_ty)?;
            }
        }

        table.insert_generics(tcx, impl_item.generics);
        match &impl_item.kind {
            rustc_hir::ImplItemKind::Fn(fn_sig, _) => {
                table.collect_from_fn_sig(fn_sig)?;
            }
            rustc_hir::ImplItemKind::Const(_, _) | rustc_hir::ImplItemKind::Type(_) => {}
        }

        Ok(table)
    }

    fn new(tcx: TyCtxt<'tcx>, sess: &'sess FluxSession) -> NameResTable<'sess, 'tcx> {
        NameResTable { sess, res: FxHashMap::default(), generics: FxHashMap::default(), tcx }
    }

    fn get(&self, sym: Symbol) -> Option<&Res> {
        self.res.get(&sym)
    }

    fn get_param_ty(&self, def_id: DefId) -> Option<ParamTy> {
        self.generics.get(&def_id).copied()
    }

    fn insert_generics(&mut self, tcx: TyCtxt, generics: &hir::Generics) {
        for (idx, param) in generics.params.iter().enumerate() {
            if let hir::GenericParamKind::Type { .. } = param.kind {
                let def_id = tcx.hir().local_def_id(param.hir_id).to_def_id();
                assert!(!self.generics.contains_key(&def_id));

                let name = param.name.ident().name;
                let param_ty = ParamTy { index: idx as u32, name };
                self.generics.insert(def_id, param_ty);
            }
        }
    }

    fn collect_from_fn_sig(&mut self, fn_sig: &hir::FnSig) -> Result<(), ErrorGuaranteed> {
        fn_sig
            .decl
            .inputs
            .iter()
            .try_for_each_exhaust(|ty| self.collect_from_ty(ty))?;

        if let hir::FnRetTy::Return(ty) = fn_sig.decl.output {
            self.collect_from_ty(ty)?;
        }

        Ok(())
    }

    fn insert_res_for_ident(
        &mut self,
        ident: Ident,
        res: rustc_hir::def::Res,
    ) -> Result<(), ErrorGuaranteed> {
        let res = self.res_from_hir_res(res, ident.span)?;
        self.res.insert(ident.name, res);
        Ok(())
    }

    fn res_from_ty(ty: rustc_middle::ty::Ty) -> Option<Res> {
        match ty.kind() {
            TyKind::Bool => Some(Res::Bool),
            TyKind::Int(int_ty) => Some(Res::Int(*int_ty)),
            TyKind::Uint(uint_ty) => Some(Res::Uint(*uint_ty)),
            TyKind::Float(float_ty) => Some(Res::Float(*float_ty)),
            TyKind::Param(param_ty) => Some(Res::Param(*param_ty)),
            TyKind::Char => Some(Res::Char),
            _ => None,
        }
    }

    fn res_from_hir_res(&self, res: hir::def::Res, span: Span) -> Result<Res, ErrorGuaranteed> {
        match res {
            hir::def::Res::Def(hir::def::DefKind::TyParam, did) => {
                Ok(Res::Param(self.get_param_ty(did).unwrap()))
            }
            hir::def::Res::Def(hir::def::DefKind::Struct | hir::def::DefKind::Enum, did) => {
                Ok(Res::Adt(did))
            }
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
            hir::def::Res::SelfTyAlias { alias_to: def_id, forbid_generic: false, .. } => {
                Ok(Res::Adt(def_id))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Str) => Ok(Res::Str),
            hir::def::Res::PrimTy(hir::PrimTy::Char) => Ok(Res::Char),
            hir::def::Res::Def(hir::def::DefKind::TyAlias, did) => {
                let ty = self.tcx.type_of(did);
                Self::res_from_ty(ty).ok_or_else(|| {
                    self.sess.emit_err(errors::UnsupportedSignature {
                        span,
                        note: format!("unsupported alias `{ty:?}`"),
                    })
                })
            }

            _ => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span,
                    note: format!("unsupported resolution `{res:?}`"),
                }))
            }
        }
    }

    fn collect_from_ty(&mut self, ty: &hir::Ty) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => self.collect_from_ty(ty),
            hir::TyKind::Ptr(mut_ty) | hir::TyKind::Ref(_, mut_ty) => {
                self.collect_from_ty(mut_ty.ty)
            }
            hir::TyKind::Tup(tys) => tys.iter().try_for_each(|ty| self.collect_from_ty(ty)),
            hir::TyKind::Path(qpath) => {
                let path = if let hir::QPath::Resolved(None, path) = qpath {
                    path
                } else {
                    return Err(self.sess.emit_err(errors::UnsupportedSignature {
                        span: qpath.span(),
                        note: "unsupported type".to_string(),
                    }));
                };

                let (ident, args) = match path.segments {
                    [hir::PathSegment { ident, args, .. }] => (ident, args),
                    _ => {
                        return Err(self.sess.emit_err(errors::UnsupportedSignature {
                            span: qpath.span(),
                            note: "multi-segment paths are not supported yet".to_string(),
                        }));
                    }
                };
                self.insert_res_for_ident(*ident, path.res)?;

                args.map(|args| args.args)
                    .iter()
                    .copied()
                    .flatten()
                    .try_for_each_exhaust(|arg| self.collect_from_generic_arg(arg))
            }
            hir::TyKind::BareFn(_)
            | hir::TyKind::Never
            | hir::TyKind::OpaqueDef(..)
            | hir::TyKind::TraitObject(..)
            | hir::TyKind::Typeof(_)
            | hir::TyKind::Infer
            | hir::TyKind::Err => Ok(()),
        }
    }

    fn collect_from_generic_arg(&mut self, arg: &hir::GenericArg) -> Result<(), ErrorGuaranteed> {
        match arg {
            hir::GenericArg::Type(ty) => self.collect_from_ty(ty),
            hir::GenericArg::Lifetime(_) => Ok(()),
            hir::GenericArg::Const(_) => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span: arg.span(),
                    note: "const generics are not supported yet".to_string(),
                }))
            }

            hir::GenericArg::Infer(_) => unreachable!(),
        }
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_syntax::surface;
    use rustc_span::{symbol::Ident, Span};

    #[derive(Diagnostic)]
    #[diag(resolver::unsupported_signature, code = "FLUX")]
    #[note]
    pub struct UnsupportedSignature {
        #[primary_span]
        pub span: Span,
        pub note: String,
    }

    #[derive(Diagnostic)]
    #[diag(resolver::unresolved_path, code = "FLUX")]
    #[help]
    pub struct UnresolvedPath {
        #[primary_span]
        pub span: Span,
        pub path: Ident,
    }

    impl UnresolvedPath {
        pub fn new(ident: surface::Ident) -> Self {
            Self { span: ident.span, path: ident }
        }
    }
}
