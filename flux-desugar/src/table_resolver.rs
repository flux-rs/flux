use flux_common::iter::IterExt;
use flux_errors::FluxSession;
use flux_middle::global_env::GlobalEnv;
use flux_syntax::surface::{self, Ident, Path, Res, Ty};
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

struct NameResTable<'genv, 'tcx> {
    res: FxHashMap<Symbol, Res>,
    generics: FxHashMap<DefId, ParamTy>,
    sess: &'genv FluxSession,
    tcx: TyCtxt<'tcx>,
}

impl<'genv, 'tcx> Resolver<'genv, 'tcx> {
    #[allow(dead_code)]

    pub fn new(genv: &GlobalEnv<'genv, 'tcx>, def_id: LocalDefId) -> Result<Self, ErrorGuaranteed> {
        let table = match genv.tcx.def_kind(def_id) {
            hir::def::DefKind::Struct | hir::def::DefKind::Enum | hir::def::DefKind::Fn => {
                NameResTable::from_item(genv, def_id)?
            }
            hir::def::DefKind::AssocFn => NameResTable::from_impl_item(genv, def_id)?,
            kind => panic!("unsupported kind {kind:?}"),
        };

        Ok(Self { sess: genv.sess, table })
    }

    #[allow(dead_code)]
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
            opaque: enum_def.opaque,
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
        let ret = self.resolve_ty(variant.ret)?;
        Ok(surface::VariantDef { fields, ret, span: variant.span })
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
            surface::Arg::Constr(bind, path, pred) => {
                Ok(surface::Arg::Constr(bind, self.resolve_path(path)?, pred))
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

    pub fn resolve_ident(&self, ident: Ident) -> Result<Res, ErrorGuaranteed> {
        if let Some(res) = self.table.get(ident.name) {
            Ok(*res)
        } else {
            Err(self.sess.emit_err(errors::UnresolvedPath::new(ident)))
        }
    }
}

impl<'genv, 'tcx> NameResTable<'genv, 'tcx> {
    fn from_item(
        genv: &GlobalEnv<'genv, 'tcx>,
        def_id: LocalDefId,
    ) -> Result<Self, ErrorGuaranteed> {
        let item = genv.tcx.hir().expect_item(def_id);
        let mut table = Self::new(genv.sess, genv.tcx);
        match &item.kind {
            ItemKind::Struct(data, generics) => {
                table.insert_generics(genv.tcx, generics);
                table
                    .res
                    .insert(item.ident.name, Res::Adt(def_id.to_def_id()));

                for field in data.fields() {
                    table.collect_from_ty(field.ty)?;
                }
            }
            ItemKind::Enum(data, generics) => {
                table.insert_generics(genv.tcx, generics);
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
                table.insert_generics(genv.tcx, generics);
                table.collect_from_fn_sig(fn_sig)?;
            }
            _ => {}
        }
        Ok(table)
    }

    fn from_impl_item(
        genv: &GlobalEnv<'genv, 'tcx>,
        def_id: LocalDefId,
    ) -> Result<Self, ErrorGuaranteed> {
        let impl_item = genv.tcx.hir().expect_impl_item(def_id);

        let mut table = Self::new(genv.sess, genv.tcx);

        // Insert generics from parent impl
        if let Some(parent_impl_did) = genv.tcx.impl_of_method(def_id.to_def_id()) {
            let parent_impl_item = genv.tcx.hir().expect_item(parent_impl_did.expect_local());
            if let ItemKind::Impl(parent) = &parent_impl_item.kind {
                table.insert_generics(genv.tcx, parent.generics);
                table.collect_from_ty(parent.self_ty)?;
            }
        }

        table.insert_generics(genv.tcx, impl_item.generics);
        match &impl_item.kind {
            rustc_hir::ImplItemKind::Fn(fn_sig, _) => {
                table.collect_from_fn_sig(fn_sig)?;
            }
            rustc_hir::ImplItemKind::Const(_, _) | rustc_hir::ImplItemKind::Type(_) => {}
        }

        Ok(table)
    }

    fn new(sess: &'genv FluxSession, tcx: TyCtxt<'tcx>) -> NameResTable<'genv, 'tcx> {
        NameResTable { sess, res: FxHashMap::default(), generics: FxHashMap::default(), tcx }
    }

    fn get(&self, sym: Symbol) -> Option<&Res> {
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
        let res = self.of_hir_res(res, ident.span)?;
        self.res.insert(ident.name, res);
        Ok(())
    }

    fn of_ty(&self, ty: rustc_middle::ty::Ty, span: Span) -> Result<Res, ErrorGuaranteed> {
        match ty.kind() {
            TyKind::Bool => Ok(Res::Bool),
            TyKind::Int(int_ty) => Ok(Res::Int(*int_ty)),
            TyKind::Uint(uint_ty) => Ok(Res::Uint(*uint_ty)),
            TyKind::Float(float_ty) => Ok(Res::Float(*float_ty)),
            TyKind::Param(pty) => Ok(Res::Param(*pty)),
            // TyKind::Adt(did, what) => todo!(),
            // TyKind::Char => todo!(),
            _ => {
            Err(self.sess.emit_err(errors::UnsupportedSignature {
                span,
                msg: "path resolved to an unsupported type",
            }))
        }
            // rustc_type_ir::TyKind::Foreign(_) => todo!(),
            // rustc_type_ir::TyKind::Str => todo!(),
            // rustc_type_ir::TyKind::Array(_, _) => todo!(),
            // rustc_type_ir::TyKind::Slice(_) => todo!(),
            // rustc_type_ir::TyKind::RawPtr(_) => todo!(),
            // rustc_type_ir::TyKind::Ref(_, _, _) => todo!(),
            // rustc_type_ir::TyKind::FnDef(_, _) => todo!(),
            // rustc_type_ir::TyKind::FnPtr(_) => todo!(),
            // rustc_type_ir::TyKind::Dynamic(_, _) => todo!(),
            // rustc_type_ir::TyKind::Closure(_, _) => todo!(),
            // rustc_type_ir::TyKind::Generator(_, _, _) => todo!(),
            // rustc_type_ir::TyKind::GeneratorWitness(_) => todo!(),
            // rustc_type_ir::TyKind::Never => todo!(),
            // rustc_type_ir::TyKind::Tuple(_) => todo!(),
            // rustc_type_ir::TyKind::Projection(_) => todo!(),
            // rustc_type_ir::TyKind::Opaque(_, _) => todo!(),
            // rustc_type_ir::TyKind::Bound(_, _) => todo!(),
            // rustc_type_ir::TyKind::Placeholder(_) => todo!(),
            // rustc_type_ir::TyKind::Infer(_) => todo!(),
            // rustc_type_ir::TyKind::Error(_) => todo!(),
        }
    }

    fn of_hir_res(&self, res: hir::def::Res, span: Span) -> Result<Res, ErrorGuaranteed> {
        match res {
            hir::def::Res::Def(hir::def::DefKind::TyParam, did) => {
                Ok(Res::Param(self.get_param_ty(did).unwrap()))
            }
            hir::def::Res::Def(hir::def::DefKind::Struct, did)
            | hir::def::Res::Def(hir::def::DefKind::Enum, did) => Ok(Res::Adt(did)),
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
            hir::def::Res::PrimTy(hir::PrimTy::Str) => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span,
                    msg: "string slices are not supported yet",
                }))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Char) => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span,
                    msg: "chars are not supported yet",
                }))
            }
            hir::def::Res::Def(hir::def::DefKind::TyAlias, did) => {
                self.of_ty(self.tcx.type_of(did), span)
            }

            _ => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span,
                    msg: "path resolved to an unsupported type",
                }))
            }
        }
    }

    fn collect_from_ty(&mut self, ty: &hir::Ty) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => self.collect_from_ty(ty),
            hir::TyKind::Ptr(mut_ty) | hir::TyKind::Rptr(_, mut_ty) => {
                self.collect_from_ty(mut_ty.ty)
            }
            hir::TyKind::Tup(tys) => tys.iter().try_for_each(|ty| self.collect_from_ty(ty)),
            hir::TyKind::Path(qpath) => {
                let path = if let hir::QPath::Resolved(None, path) = qpath {
                    path
                } else {
                    return Err(self.sess.emit_err(errors::UnsupportedSignature {
                        span: qpath.span(),
                        msg: "unsupported type",
                    }));
                };

                let (ident, args) = match path.segments {
                    [hir::PathSegment { ident, args, .. }] => (ident, args),
                    _ => {
                        return Err(self.sess.emit_err(errors::UnsupportedSignature {
                            span: qpath.span(),
                            msg: "multi-segment paths are not supported yet",
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
            hir::GenericArg::Lifetime(_) => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span: arg.span(),
                    msg: "lifetime parameters are not supported yet",
                }))
            }
            hir::GenericArg::Const(_) => {
                Err(self.sess.emit_err(errors::UnsupportedSignature {
                    span: arg.span(),
                    msg: "const generics are not supported yet",
                }))
            }

            hir::GenericArg::Infer(_) => unreachable!(),
        }
    }
}

pub mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::rustc::ty::Mutability;
    use flux_syntax::surface::{self, RefKind, Res};
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{symbol::Ident, Span};

    #[derive(Diagnostic)]
    #[diag(resolver::unsupported_signature, code = "FLUX")]
    pub struct UnsupportedSignature {
        #[primary_span]
        #[label]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag(resolver::unresolved_path, code = "FLUX")]
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

    #[derive(Diagnostic)]
    #[diag(resolver::mismatched_fields, code = "FLUX")]
    pub struct FieldCountMismatch {
        #[primary_span]
        pub span: Span,
        pub rust_fields: usize,
        pub flux_fields: usize,
    }

    impl FieldCountMismatch {
        pub fn new(span: Span, rust_fields: usize, flux_fields: usize) -> Self {
            Self { span, rust_fields, flux_fields }
        }
    }

    #[derive(Diagnostic)]
    #[diag(resolver::mismatched_args, code = "FLUX")]
    pub struct ArgCountMismatch {
        #[primary_span]
        pub span: Span,
        pub rust_args: usize,
        pub flux_args: usize,
    }

    impl ArgCountMismatch {
        pub fn new(span: Span, rust_args: usize, flux_args: usize) -> Self {
            Self { span, rust_args, flux_args }
        }
    }

    #[derive(Diagnostic)]
    #[diag(resolver::mismatched_type, code = "FLUX")]
    pub struct MismatchedType {
        #[primary_span]
        pub span: Span,
        pub rust_type: String,
        pub flux_type: Ident,
    }

    impl MismatchedType {
        pub fn new(tcx: TyCtxt, rust_res: Res, flux_type: Ident) -> Self {
            let rust_type = print_res(tcx, rust_res);
            Self { span: flux_type.span, rust_type, flux_type }
        }
    }

    #[derive(Diagnostic)]
    #[diag(resolver::mutability_mismatch, code = "FLUX")]
    pub struct RefKindMismatch {
        #[primary_span]
        pub span: Span,
        pub flux_ref: &'static str,
        pub rust_ref: &'static str,
    }

    impl RefKindMismatch {
        pub fn new(span: Span, ref_kind: RefKind, mutability: Mutability) -> Self {
            Self {
                span,
                flux_ref: match ref_kind {
                    RefKind::Mut => "&mut",
                    RefKind::Shr => "&",
                },
                rust_ref: match mutability {
                    Mutability::Mut => "&mut",
                    Mutability::Not => "&",
                },
            }
        }
    }

    fn print_res(tcx: TyCtxt, res: Res) -> String {
        match res {
            Res::Bool => "bool".to_string(),
            Res::Int(int_ty) => int_ty.name_str().to_string(),
            Res::Uint(uint_ty) => uint_ty.name_str().to_string(),
            Res::Float(float_ty) => float_ty.name_str().to_string(),
            Res::Adt(def_id) => print_def_id(tcx, def_id),
            Res::Param(_) => todo!(),
        }
    }

    fn print_def_id(tcx: TyCtxt, def_id: DefId) -> String {
        let crate_name = tcx.crate_name(def_id.krate);
        format!("{crate_name}{}", tcx.def_path(def_id).to_string_no_crate_verbose())
    }
}
