use liquid_rust_common::ty::Ty;
use liquid_rust_parser::parse_ty;

use rustc_ast::ast::{AttrItem, AttrKind, Attribute, MacArgs};
use rustc_ast_pretty::pprust::tts_to_string;
use rustc_hir::{
    def_id::DefId, itemlikevisit::ItemLikeVisitor, ImplItem, Item, ItemKind, TraitItem,
};
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;

pub struct DefIdCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    annotations: HashMap<DefId, Option<Ty>>,
}

impl<'tcx> DefIdCollector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            annotations: HashMap::default(),
        }
    }

    pub fn annotations(self) -> HashMap<DefId, Option<Ty>> {
        self.annotations
    }
}

impl<'hir> ItemLikeVisitor<'hir> for DefIdCollector<'_> {
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

fn extract_annotations(attrs: &[Attribute]) -> Option<Ty> {
    for attr in attrs {
        if let AttrKind::Normal(AttrItem { path, args, .. }) = &attr.kind {
            let mut path = path.segments.iter().map(|segment| segment.ident.as_str());

            match path.next() {
                Some(fst) if fst == "liquid" => match path.next() {
                    Some(snd) => {
                        if snd == "ty" {
                            if let MacArgs::Delimited(_, _, token_stream) = args {
                                let ty_string = tts_to_string(token_stream);

                                let ty = parse_ty(&ty_string.trim_matches('"'))
                                    .expect("Parsing type annotation failed");

                                return Some(ty);
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
