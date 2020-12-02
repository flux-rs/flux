use liquid_rust_parser::{parse_ty, ParseResult};
use liquid_rust_ty::Ty;

use rustc_ast::ast::{AttrItem, AttrKind, Attribute, MacArgs};
use rustc_ast_pretty::pprust::tts_to_string;
use rustc_hir::{
    def_id::DefId, itemlikevisit::ItemLikeVisitor, ImplItem, Item, ItemKind, TraitItem,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{BytePos, Span};
use std::collections::HashMap;

pub struct DefIdCollector<'tcx, V> {
    tcx: TyCtxt<'tcx>,
    annotations: HashMap<DefId, Option<ParseResult<(Ty<V>, Span), Span>>>,
}

impl<'tcx, V> DefIdCollector<'tcx, V> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            annotations: HashMap::default(),
        }
    }

    pub fn annotations(self) -> HashMap<DefId, Option<ParseResult<(Ty<V>, Span), Span>>> {
        self.annotations
    }
}

impl<'hir, V: Copy> ItemLikeVisitor<'hir> for DefIdCollector<'_, V> {
    fn visit_item(&mut self, item: &'hir Item<'hir>) {
        if let ItemKind::Fn(..) = item.kind {
            let def_id = self.tcx.hir().local_def_id(item.hir_id).to_def_id();

            self.annotations
                .insert(def_id, extract_annotations(item.attrs));
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'hir TraitItem<'hir>) {}
    fn visit_impl_item(&mut self, _impl_item: &'hir ImplItem<'hir>) {}
}

fn extract_annotations<V: Copy>(attrs: &[Attribute]) -> Option<ParseResult<(Ty<V>, Span), Span>> {
    for attr in attrs {
        if let AttrKind::Normal(AttrItem { path, args, .. }, ..) = &attr.kind {
            let mut path = path.segments.iter().map(|segment| segment.ident.as_str());

            match path.next() {
                Some(fst) if fst == "liquid" => match path.next() {
                    Some(snd) => {
                        if snd == "ty" {
                            if let MacArgs::Delimited(delim_span, _, token_stream) = args {
                                let ty_string = tts_to_string(token_stream);
                                let ty = parse_ty(&ty_string.trim_matches('"')).map_err(|err| {
                                    err.map_span(|span| {
                                        let open = delim_span.open;
                                        let lo = open.lo() + BytePos(2 + span.start as u32);
                                        let hi = open.lo() + BytePos(2 + span.end as u32);
                                        return Span::new(lo, hi, open.ctxt());
                                    })
                                });
                                return Some(ty.map(|ty| (ty, delim_span.entire())));
                            } else {
                                panic!("Type annotations must have the syntax `#[liquid::ty(\"<type>\")]`");
                            }
                        } else {
                            panic!("Unsupported annotation kind {}", snd);
                        }
                    }
                    _ => panic!("Missing annotation kind"),
                },
                _ => (),
            }
        }
    }
    None
}
