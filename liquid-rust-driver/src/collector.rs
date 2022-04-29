use std::collections::HashMap;

use itertools::Itertools;
use liquid_rust_common::iter::IterExt;
use liquid_rust_syntax::{
    parse_assert_behavior, parse_fn_surface_sig, parse_qualifier, parse_refined_by, parse_ty,
    surface, ParseErrorKind, ParseResult,
};
use rustc_ast::{tokenstream::TokenStream, AttrItem, AttrKind, Attribute, MacArgs};
use rustc_errors::ErrorReported;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def_id::LocalDefId, itemlikevisit::ItemLikeVisitor, ForeignItem, ImplItem, ImplItemKind, Item,
    ItemKind, TraitItem, VariantData,
};
use rustc_middle::ty::TyCtxt;
use rustc_session::{Session, SessionDiagnostic};
use rustc_span::Span;

pub(crate) struct SpecCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    specs: Specs,
    sess: &'a Session,
    error_reported: bool,
}

pub(crate) struct Specs {
    pub fns: FxHashMap<LocalDefId, FnSpec>,
    pub adts: FxHashMap<LocalDefId, surface::AdtDef>,
    pub qualifs: Vec<surface::Qualifier>,
    pub assert_behavior: Option<surface::AssertBehavior>,
}

pub(crate) struct FnSpec {
    pub fn_sig: Option<surface::FnSig>,
    pub assume: bool,
}

impl<'tcx, 'a> SpecCollector<'tcx, 'a> {
    pub(crate) fn collect(tcx: TyCtxt<'tcx>, sess: &'a Session) -> Result<Specs, ErrorReported> {
        let mut collector = Self { tcx, sess, specs: Specs::new(), error_reported: false };

        tcx.hir().visit_all_item_likes(&mut collector);

        collector.parse_crate_spec(tcx.hir().krate_attrs())?;

        if collector.error_reported {
            Err(ErrorReported)
        } else {
            Ok(collector.specs)
        }
    }

    fn parse_fn_spec(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorReported> {
        let mut attrs = self.parse_liquid_attrs(attrs)?;
        self.report_dups(&attrs)?;
        // TODO(nilehmann) error if it has non-fun attrs

        let assume = attrs.assume();
        let fn_sig = attrs.fn_sig();

        self.specs.fns.insert(def_id, FnSpec { fn_sig, assume });
        Ok(())
    }

    fn parse_struct_def(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
        data: &VariantData,
    ) -> Result<(), ErrorReported> {
        let mut attrs = self.parse_liquid_attrs(attrs)?;
        self.report_dups(&attrs)?;
        // TODO(nilehmann) error on field attrs if opaque
        // TODO(nilehmann) error if it has non-struct attrs

        let opaque = attrs.opaque();

        let refined_by = attrs.refined_by();

        let fields = data
            .fields()
            .iter()
            .map(|field| self.parse_field_spec(self.tcx.hir().attrs(field.hir_id)))
            .try_collect_exhaust()?;

        self.specs
            .adts
            .insert(def_id, surface::AdtDef { refined_by, fields, opaque });

        Ok(())
    }

    fn parse_crate_spec(&mut self, attrs: &[Attribute]) -> Result<(), ErrorReported> {
        let mut attrs = self.parse_liquid_attrs(attrs)?;
        let mut qualifiers = attrs.qualifiers();
        let assert_behavior = attrs.assert_behavior();
        self.specs.assert_behavior = assert_behavior;
        self.specs.qualifs.append(&mut qualifiers);
        Ok(())
    }

    fn parse_field_spec(
        &mut self,
        attrs: &[Attribute],
    ) -> Result<Option<surface::Ty>, ErrorReported> {
        let mut attrs = self.parse_liquid_attrs(attrs)?;
        self.report_dups(&attrs)?;
        Ok(attrs.field())
    }

    fn parse_liquid_attrs(&mut self, attrs: &[Attribute]) -> Result<LiquidAttrs, ErrorReported> {
        let attrs: Vec<_> = attrs
            .iter()
            .filter_map(|attr| {
                if let AttrKind::Normal(attr_item, ..) = &attr.kind {
                    match &attr_item.path.segments[..] {
                        [first, ..] if first.ident.as_str() == "lr" => Some(attr_item),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .map(|attr_item| self.parse_liquid_attr(attr_item))
            .try_collect_exhaust()?;

        Ok(LiquidAttrs::new(attrs))
    }

    fn parse_liquid_attr(&mut self, attr_item: &AttrItem) -> Result<LiquidAttr, ErrorReported> {
        let segment = match &attr_item.path.segments[..] {
            [_, segment] => segment,
            _ => return self.emit_err(errors::InvalidAttr { span: attr_item.span() }),
        };

        let kind = match (segment.ident.as_str(), &attr_item.args) {
            ("sig", MacArgs::Delimited(span, _, tokens)) => {
                let fn_sig = self.parse(tokens.clone(), span.entire(), parse_fn_surface_sig)?;
                // print!("LR::SIG {:#?} \n", fn_sig);
                LiquidAttrKind::FnSig(fn_sig)
            }
            ("qualifier", MacArgs::Delimited(span, _, tokens)) => {
                let qualifer = self.parse(tokens.clone(), span.entire(), parse_qualifier)?;
                LiquidAttrKind::Qualifier(qualifer)
            }
            ("assert_behavior", MacArgs::Delimited(span, _, tokens)) => {
                let assert_behavior =
                    self.parse(tokens.clone(), span.entire(), parse_assert_behavior)?;
                LiquidAttrKind::AssertBehavior(assert_behavior)
            }
            ("refined_by", MacArgs::Delimited(span, _, tokens)) => {
                let refined_by = self.parse(tokens.clone(), span.entire(), parse_refined_by)?;
                LiquidAttrKind::RefinedBy(refined_by)
            }
            ("field", MacArgs::Delimited(span, _, tokens)) => {
                let ty = self.parse(tokens.clone(), span.entire(), parse_ty)?;
                LiquidAttrKind::Field(ty)
            }
            ("opaque", MacArgs::Empty) => LiquidAttrKind::Opaque,
            ("assume", MacArgs::Empty) => LiquidAttrKind::Assume,
            _ => return self.emit_err(errors::InvalidAttr { span: attr_item.span() }),
        };
        Ok(LiquidAttr { kind, span: attr_item.span() })
    }

    fn parse<T>(
        &mut self,
        tokens: TokenStream,
        input_span: Span,
        parser: impl FnOnce(TokenStream, Span) -> ParseResult<T>,
    ) -> Result<T, ErrorReported> {
        match parser(tokens, input_span) {
            Ok(result) => Ok(result),
            Err(err) => {
                let msg = match err.kind {
                    ParseErrorKind::UnexpectedEOF => "type annotation ended unexpectedly",
                    ParseErrorKind::UnexpectedToken => "unexpected token",
                    ParseErrorKind::IntTooLarge => "integer literal is too large",
                };

                self.emit_err(errors::SyntaxErr { span: err.span, msg })
            }
        }
    }

    fn report_dups(&mut self, attrs: &LiquidAttrs) -> Result<(), ErrorReported> {
        let mut has_dups = false;
        for (name, dups) in attrs.dups() {
            has_dups = true;
            for attr in dups {
                self.sess
                    .emit_err(errors::DuplicatedAttr { span: attr.span, name });
            }
        }
        if has_dups {
            self.error_reported = true;
            Err(ErrorReported)
        } else {
            Ok(())
        }
    }

    fn emit_err<T>(&mut self, err: impl SessionDiagnostic<'a>) -> Result<T, ErrorReported> {
        self.error_reported = true;
        self.sess.emit_err(err);
        Err(ErrorReported)
    }
}

impl<'hir> ItemLikeVisitor<'hir> for SpecCollector<'_, '_> {
    fn visit_item(&mut self, item: &'hir Item<'hir>) {
        match &item.kind {
            ItemKind::Fn(..) => {
                let hir_id = item.hir_id();
                let attrs = self.tcx.hir().attrs(hir_id);
                let _ = self.parse_fn_spec(item.def_id, attrs);
            }
            ItemKind::Struct(data, ..) => {
                let hir_id = item.hir_id();
                let attrs = self.tcx.hir().attrs(hir_id);
                let _ = self.parse_struct_def(item.def_id, attrs, data);
            }
            ItemKind::Mod(..) => {
                // TODO: Parse mod level attributes
            }
            _ => (),
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'hir TraitItem<'hir>) {}
    fn visit_impl_item(&mut self, item: &'hir ImplItem<'hir>) {
        if let ImplItemKind::Fn(..) = &item.kind {
            let hir_id = item.hir_id();
            let attrs = self.tcx.hir().attrs(hir_id);
            let _ = self.parse_fn_spec(item.def_id, attrs);
        }
    }
    fn visit_foreign_item(&mut self, _foreign_item: &'hir ForeignItem<'hir>) {}
}

impl Specs {
    fn new() -> Specs {
        Specs {
            fns: FxHashMap::default(),
            adts: FxHashMap::default(),
            qualifs: Vec::default(),
            assert_behavior: None,
        }
    }
}

#[derive(Debug)]
struct LiquidAttrs {
    map: HashMap<&'static str, Vec<LiquidAttr>>,
}

#[derive(Debug)]
struct LiquidAttr {
    kind: LiquidAttrKind,
    span: Span,
}

#[derive(Debug)]
enum LiquidAttrKind {
    Assume,
    Opaque,
    FnSig(surface::FnSig),
    RefinedBy(surface::Params),
    Qualifier(surface::Qualifier),
    Field(surface::Ty),
    AssertBehavior(surface::AssertBehavior),
}

macro_rules! read_attr {
    ($self:expr, $name:literal, $kind:ident) => {
        $self
            .map
            .remove($name)
            .unwrap_or_else(|| vec![])
            .into_iter()
            .find_map(
                |attr| if let LiquidAttrKind::$kind(sig) = attr.kind { Some(sig) } else { None },
            )
    };
}

// like read_attr, but returns all valid attributes
macro_rules! read_all_attrs {
    ($self:expr, $name:literal, $kind:ident) => {
        $self
            .map
            .remove($name)
            .unwrap_or_else(|| vec![])
            .into_iter()
            .filter_map(
                |attr| if let LiquidAttrKind::$kind(sig) = attr.kind { Some(sig) } else { None },
            )
            .collect()
    };
}

impl LiquidAttrs {
    fn new(attrs: Vec<LiquidAttr>) -> Self {
        LiquidAttrs { map: attrs.into_iter().into_group_map_by(|attr| attr.kind.name()) }
    }

    fn dups(&self) -> impl Iterator<Item = (&'static str, &[LiquidAttr])> {
        self.map
            .iter()
            .filter(|(_, attrs)| attrs.len() > 1)
            .map(|(name, attrs)| (*name, &attrs[1..]))
    }

    fn assume(&mut self) -> bool {
        self.map.get("assume").is_some()
    }

    fn opaque(&mut self) -> bool {
        self.map.get("opaque").is_some()
    }

    fn fn_sig(&mut self) -> Option<surface::FnSig> {
        read_attr!(self, "ty", FnSig)
    }

    fn qualifiers(&mut self) -> Vec<surface::Qualifier> {
        read_all_attrs!(self, "qualifier", Qualifier)
    }

    fn refined_by(&mut self) -> Option<surface::Params> {
        read_attr!(self, "refined_by", RefinedBy)
    }

    fn field(&mut self) -> Option<surface::Ty> {
        read_attr!(self, "field", Field)
    }

    fn assert_behavior(&mut self) -> Option<surface::AssertBehavior> {
        read_attr!(self, "assert_behavior", AssertBehavior)
    }
}

impl LiquidAttrKind {
    fn name(&self) -> &'static str {
        match self {
            LiquidAttrKind::Assume => "assume",
            LiquidAttrKind::Opaque => "opaque",
            LiquidAttrKind::FnSig(_) => "ty",
            LiquidAttrKind::RefinedBy(_) => "refined_by",
            LiquidAttrKind::Qualifier(_) => "qualifier",
            LiquidAttrKind::Field(_) => "field",
            LiquidAttrKind::AssertBehavior(_) => "assert_behavior",
        }
    }
}

mod errors {
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct DuplicatedAttr {
        #[message = "duplicated attribute `{name}`"]
        pub span: Span,
        pub name: &'static str,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct InvalidAttr {
        #[message = "invalid liquid attribute"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct SyntaxErr {
        #[message = "Syntax Error: {msg}"]
        pub span: Span,
        pub msg: &'static str,
    }
}
