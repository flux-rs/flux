use rustc_ast::ast::{AttrItem, AttrKind, Attribute, MacArgs};
use rustc_ast_pretty::pprust::tts_to_string;
use rustc_hir::{itemlikevisit::ItemLikeVisitor, ImplItem, Item, ItemKind, TraitItem};
use rustc_middle::ty::TyCtxt;

use crate::item::{Annotation, Function};

pub struct MyVisitor<'tcx> {
    fns: Vec<Function<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'hir, 'tcx> ItemLikeVisitor<'hir> for MyVisitor<'tcx> {
    fn visit_item(&mut self, item: &'hir Item<'hir>) {
        if let ItemKind::Fn(..) = item.kind {
            let def_id = self.tcx.hir().local_def_id(item.hir_id);
            let body = self.tcx.optimized_mir(def_id).clone();

            let attrs = item.attrs;
            let anns = self.get_anns(attrs);

            let func = Function::new(body, anns);
            println!("\n{}:", item.ident);
            println!("{:?}", func);

            self.push_fn(func);
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'hir TraitItem<'hir>) {}
    fn visit_impl_item(&mut self, _impl_item: &'hir ImplItem<'hir>) {}
}

impl<'tcx> MyVisitor<'tcx> {
    pub fn from_tcx(tcx: TyCtxt<'tcx>) -> Self {
        Self { fns: vec![], tcx }
    }

    fn push_fn(&mut self, func: Function<'tcx>) {
        self.fns.push(func);
    }

    fn get_anns(&mut self, attrs: &[Attribute]) -> Vec<Annotation> {
        let mut anns = vec![];

        for attr in attrs {
            if let AttrKind::Normal(AttrItem { path, args, .. }) = &attr.kind {
                let path = path
                    .segments
                    .iter()
                    .map(|segment| segment.ident.as_str())
                    .collect::<Vec<_>>();

                match path.get(0) {
                    Some(fst) if *fst == "liquid" => match path.get(1) {
                        Some(snd) if *snd == "ty" => {
                            if let MacArgs::Delimited(_, _, token_stream) = args {
                                let ty_string = tts_to_string(token_stream);
                                let (rem, ty) = crate::refinements::parser::parse_ty(
                                    &ty_string.trim_matches('"'),
                                )
                                .unwrap();

                                assert!(rem.is_empty());

                                anns.push(Annotation::Ty(ty));
                            } else {
                                panic!();
                            }
                        }
                        _ => panic!(),
                    },
                    _ => (),
                }
            }
        }

        anns
    }
}
