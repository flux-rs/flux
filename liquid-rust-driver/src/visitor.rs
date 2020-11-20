use crate::lower::LowerMap;

use liquid_rust_lang::{ir::FuncId, ty::Ty, tycheck::TyContext};
use liquid_rust_parser::parse_ty;

use rustc_ast::ast::{AttrItem, AttrKind, Attribute, MacArgs};
use rustc_ast_pretty::pprust::tts_to_string;
use rustc_hir::{
    def_id::DefId, itemlikevisit::ItemLikeVisitor, ImplItem, Item, ItemKind, TraitItem,
};
use rustc_middle::ty::TyCtxt;

pub struct DefIdCollector<'tcx, 'low> {
    tcx: TyCtxt<'tcx>,
    ctx: &'low mut TyContext,
    func_ids: &'low mut LowerMap<DefId, FuncId>,
}

impl<'tcx, 'low> DefIdCollector<'tcx, 'low> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        ctx: &'low mut TyContext,
        func_ids: &'low mut LowerMap<DefId, FuncId>,
    ) -> Self {
        Self { tcx, ctx, func_ids }
    }
}

impl<'hir> ItemLikeVisitor<'hir> for DefIdCollector<'_, '_> {
    fn visit_item(&mut self, item: &'hir Item<'hir>) {
        if let ItemKind::Fn(..) = item.kind {
            let def_id = self.tcx.hir().local_def_id(item.hir_id).to_def_id();

            let func_id = self.func_ids.store(def_id);

            if let Some(ty) = extract_annotations(item.attrs, self.ctx) {
                self.ctx.store_func_ty(func_id, ty);
            }
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'hir TraitItem<'hir>) {}
    fn visit_impl_item(&mut self, _impl_item: &'hir ImplItem<'hir>) {}
}

fn extract_annotations(attrs: &[Attribute], ctx: &TyContext) -> Option<Ty> {
    for attr in attrs {
        if let AttrKind::Normal(AttrItem { path, args, .. }) = &attr.kind {
            let mut path = path.segments.iter().map(|segment| segment.ident.as_str());

            match path.next() {
                Some(fst) if fst == "liquid" => match path.next() {
                    Some(snd) => {
                        if snd == "ty" {
                            if let MacArgs::Delimited(_, _, token_stream) = args {
                                let ty_string = tts_to_string(token_stream);

                                let ast_ty = parse_ty(&ty_string.trim_matches('"'))
                                    .expect("Parsing type annotation failed");

                                let ty = ctx.resolve_ty(&ast_ty).expect("Type resolution failed");

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
