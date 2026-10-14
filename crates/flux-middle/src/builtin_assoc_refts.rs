//! Associated refinements of builtin traits, e.g., `<T as Sized>::size_of()`.
//!
//! These traits are defined in `core` and have no Flux spec, so their associated refinements
//! (name, sort, and body) are declared here instead, in [`BUILTIN_ASSOC_REFTS`].
//!
//! Users cannot implement these traits (or, for `FnOnce`, the impls we care about are builtin),
//! so the body of each associated refinement is computed from the structure of the `Self` type
//! alone, without going through trait selection. When the type is not concrete enough to do so,
//! each associated refinement says what to do instead, see [`Fallback`].

use flux_arc_interner::List;
use flux_common::bug;
use flux_rustc_bridge::lowering::Lower as _;
use flux_syntax::symbols::sym;
use rustc_attr_ir::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self as rustc_ty, TypingEnv, layout::LayoutCx};
use rustc_span::{DUMMY_SP, Symbol};

use crate::{
    def_id::FluxDefId,
    global_env::GlobalEnv,
    queries::QueryResult,
    query_bug,
    rty::{
        self, AliasReft, AssocRefinements, AssocReft, BaseTy, BinOp, Expr, GenericArgs, RefineArgs,
        Sort, refining::Refiner,
    },
};

/// A builtin associated refinement `fn name(inputs) -> output` of the trait `trait_`.
struct BuiltinAssocReft {
    trait_: LangItem,
    name: Symbol,
    inputs: &'static [Sort],
    output: Sort,
    /// Computes the body of the associated refinement for the `Self` type of an alias, or returns
    /// `None` if it cannot be computed (e.g., for a type parameter), in which case we use the
    /// `fallback`. The inputs are bound variables of the body, in order.
    body: BodyFn,
    fallback: Fallback,
}

/// What to do with an alias whose body cannot be computed from its `Self` type.
#[derive(Clone, Copy)]
enum Fallback {
    /// Leave the alias uninterpreted. For traits that users cannot implement, selection cannot tell
    /// us anything more, and it fails outright for types that don't implement the trait, e.g.,
    /// extern types are not `MetaSized`.
    Opaque,
    /// Normalize the alias through trait selection like any other, e.g., `Box<F>: FnOnce` is
    /// implemented by a regular impl in `alloc`.
    Select,
}

/// The result of [`GlobalEnv::builtin_assoc_reft_body`].
pub enum BuiltinAssocReftBody {
    Body(rty::Lambda),
    /// The alias must be left uninterpreted.
    Opaque,
    /// The alias must be normalized through trait selection, either because it is not a builtin
    /// associated refinement or because of [`Fallback::Select`].
    Select,
}

type BodyFn = for<'genv, 'tcx> fn(&BodyCx<'genv, 'tcx>, &AliasReft) -> QueryResult<Option<Expr>>;

static BUILTIN_ASSOC_REFTS: &[BuiltinAssocReft] = &[
    BuiltinAssocReft {
        trait_: LangItem::FnOnce,
        name: sym::no_panic,
        inputs: &[],
        output: Sort::Bool,
        body: fn_once_no_panic,
        fallback: Fallback::Select,
    },
    BuiltinAssocReft {
        trait_: LangItem::Sized,
        name: sym::size_of,
        inputs: &[],
        output: Sort::Int,
        body: sized_size_of,
        fallback: Fallback::Opaque,
    },
    BuiltinAssocReft {
        trait_: LangItem::Sized,
        name: sym::align_of,
        inputs: &[],
        output: Sort::Int,
        body: sized_align_of,
        fallback: Fallback::Opaque,
    },
    // The input is the pointer metadata: the length for slices and `str`, the vtable pointer for
    // `dyn Trait`, and unused for sized types.
    BuiltinAssocReft {
        trait_: LangItem::MetaSized,
        name: sym::size_of_val,
        inputs: &[Sort::Int],
        output: Sort::Int,
        body: meta_sized_size_of_val,
        fallback: Fallback::Opaque,
    },
    BuiltinAssocReft {
        trait_: LangItem::MetaSized,
        name: sym::align_of_val,
        inputs: &[Sort::Int],
        output: Sort::Int,
        body: meta_sized_align_of_val,
        fallback: Fallback::Opaque,
    },
];

impl BuiltinAssocReft {
    fn find(trait_: LangItem, name: Symbol) -> Option<&'static Self> {
        BUILTIN_ASSOC_REFTS
            .iter()
            .find(|reft| reft.trait_ == trait_ && reft.name == name)
    }

    fn fsort(&self) -> rty::FuncSort {
        rty::FuncSort::new(self.inputs.to_vec(), self.output.clone())
    }
}

impl<'tcx> GlobalEnv<'_, 'tcx> {
    /// The associated refinements of a builtin trait, or `None` if `def_id` is not one.
    pub fn builtin_assoc_refts(self, def_id: DefId) -> Option<AssocRefinements> {
        let tcx = self.tcx();
        let trait_ = tcx.as_lang_item(def_id)?;
        let items: List<_> = BUILTIN_ASSOC_REFTS
            .iter()
            .filter(|reft| reft.trait_ == trait_)
            .map(|reft| {
                AssocReft::new(self.builtin_assoc_reft_id(reft), false, tcx.def_span(def_id))
            })
            .collect();
        if items.is_empty() {
            return None;
        }
        Some(AssocRefinements { items })
    }

    pub fn builtin_assoc_reft_sort(
        self,
        assoc_id: FluxDefId,
    ) -> Option<rty::EarlyBinder<rty::FuncSort>> {
        Some(rty::EarlyBinder(self.lookup_builtin_assoc_reft(assoc_id)?.fsort()))
    }

    /// Returns the alias `<args as trait_>::name(refine_args)` for a builtin associated
    /// refinement. Panics if no such builtin associated refinement exists.
    pub fn builtin_alias(
        self,
        trait_: LangItem,
        name: Symbol,
        args: GenericArgs,
        refine_args: RefineArgs,
    ) -> Expr {
        let reft = BuiltinAssocReft::find(trait_, name)
            .unwrap_or_else(|| bug!("missing builtin assoc reft `{name}` for `{trait_:?}`"));
        let assoc_id = self.builtin_assoc_reft_id(reft);
        Expr::alias(AliasReft { assoc_id, args }, refine_args)
    }

    /// Returns how to normalize `alias_reft` if it is a builtin associated refinement, see
    /// [`BuiltinAssocReftBody`]. `item` is the item in which the alias is being normalized.
    pub fn builtin_assoc_reft_body(
        self,
        item: DefId,
        typing_env: TypingEnv<'tcx>,
        alias_reft: &AliasReft,
    ) -> QueryResult<BuiltinAssocReftBody> {
        let Some(reft) = self.lookup_builtin_assoc_reft(alias_reft.assoc_id) else {
            return Ok(BuiltinAssocReftBody::Select);
        };
        let refiner = Refiner::default_for_item(self, item)?;
        let cx = BodyCx { genv: self, typing_env, refiner };
        let body = match (reft.body)(&cx, alias_reft)? {
            Some(body) => {
                BuiltinAssocReftBody::Body(rty::Lambda::bind_with_fsort(body, reft.fsort()))
            }
            None if let Fallback::Opaque = reft.fallback => BuiltinAssocReftBody::Opaque,
            None => BuiltinAssocReftBody::Select,
        };
        Ok(body)
    }

    fn lookup_builtin_assoc_reft(self, assoc_id: FluxDefId) -> Option<&'static BuiltinAssocReft> {
        let trait_ = self.tcx().as_lang_item(assoc_id.parent())?;
        BuiltinAssocReft::find(trait_, assoc_id.name())
    }

    #[allow(
        clippy::disallowed_methods,
        reason = "this file is the source of truth for builtin assoc refts def ids"
    )]
    fn builtin_assoc_reft_id(self, reft: &BuiltinAssocReft) -> FluxDefId {
        FluxDefId::new(self.tcx().require_lang_item(reft.trait_, DUMMY_SP), reft.name)
    }
}

/// The context in which the body of a builtin associated refinement is computed.
struct BodyCx<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    typing_env: TypingEnv<'tcx>,
    refiner: Refiner<'genv, 'tcx>,
}

impl<'tcx> BodyCx<'_, 'tcx> {
    fn tcx(&self) -> rustc_ty::TyCtxt<'tcx> {
        self.genv.tcx()
    }

    fn self_ty(&self, alias_reft: &AliasReft) -> rustc_ty::Ty<'tcx> {
        alias_reft.to_rustc_trait_ref(self.tcx()).self_ty()
    }

    /// `<ty as trait_>::name(refine_args)` for a rustc type `ty`.
    fn alias(
        &self,
        trait_: LangItem,
        name: Symbol,
        ty: rustc_ty::Ty<'tcx>,
        refine_args: RefineArgs,
    ) -> QueryResult<Expr> {
        let tcx = self.tcx();
        let trait_id = tcx.require_lang_item(trait_, DUMMY_SP);
        let args = tcx
            .mk_args(&[ty.into()])
            .lower(tcx)
            .map_err(|reason| query_bug!(trait_id, "{reason:?}"))?;
        let args = self.refiner.refine_generic_args(trait_id, &args)?;
        Ok(self.genv.builtin_alias(trait_, name, args, refine_args))
    }

    fn layout(
        &self,
        ty: rustc_ty::Ty<'tcx>,
    ) -> Option<rustc_abi::TyAndLayout<'tcx, rustc_ty::Ty<'tcx>>> {
        // A type can have a layout that depends on generic parameters (`W<T>`, `[T; 2]`, ...), so
        // `layout_of` may fail with `TooGeneric`. Leaving the alias abstract is always sound.
        self.tcx()
            .layout_of(self.typing_env.as_query_input(ty))
            .ok()
    }
}

/// Closures record whether they may panic; fn items and fn pointers may always panic. For anything
/// else (e.g., a type parameter `F: FnOnce`) we defer to selection.
fn fn_once_no_panic(_: &BodyCx, alias_reft: &AliasReft) -> QueryResult<Option<Expr>> {
    let body = match alias_reft.self_ty().as_bty_skipping_binder() {
        BaseTy::Closure(_, _, _, true) => Expr::tt(),
        BaseTy::Closure(_, _, _, false) => Expr::ff(),
        BaseTy::FnDef(..) | BaseTy::FnPtr(..) => Expr::ff(),
        _ => return Ok(None),
    };
    Ok(Some(body))
}

fn sized_size_of(cx: &BodyCx, alias_reft: &AliasReft) -> QueryResult<Option<Expr>> {
    let size = cx
        .layout(cx.self_ty(alias_reft))
        .map(|layout| layout.size.bytes());
    Ok(size.map(int))
}

fn sized_align_of(cx: &BodyCx, alias_reft: &AliasReft) -> QueryResult<Option<Expr>> {
    let align = cx
        .layout(cx.self_ty(alias_reft))
        .map(|layout| layout.align.abi.bytes());
    Ok(align.map(int))
}

/// - sized types ignore the metadata: `Sized::size_of()`,
/// - `[E]`: `meta * E::size_of()`,
/// - `str`: `meta`,
/// - a struct or tuple whose tail is a slice or `str`:
///   `round_up(offset_of_tail + Tail::size_of_val(meta), align)`.
///
/// Anything else (`dyn Trait`, a type parameter `T: ?Sized`, extern types, ...) is opaque.
fn meta_sized_size_of_val(cx: &BodyCx, alias_reft: &AliasReft) -> QueryResult<Option<Expr>> {
    let self_ty = cx.self_ty(alias_reft);
    let meta = Expr::nu();
    if self_ty.is_sized(cx.tcx(), cx.typing_env) {
        return cx
            .alias(LangItem::Sized, sym::size_of, self_ty, List::empty())
            .map(Some);
    }
    let body = match self_ty.kind() {
        rustc_ty::Slice(elem) => {
            let elem_size = cx.alias(LangItem::Sized, sym::size_of, *elem, List::empty())?;
            Expr::binary_op(BinOp::Mul(Sort::Int), meta, elem_size)
        }
        rustc_ty::Str => meta,
        rustc_ty::Adt(..) | rustc_ty::Tuple(..) => {
            let Some(layout) = dst_layout(cx, self_ty) else { return Ok(None) };
            let tail_idx = layout.fields.count() - 1;
            let offset = layout.fields.offset(tail_idx).bytes();
            let tail = layout
                .field(&LayoutCx::new(cx.tcx(), cx.typing_env), tail_idx)
                .ty;
            let tail_size =
                cx.alias(LangItem::MetaSized, sym::size_of_val, tail, List::singleton(meta))?;
            let size = Expr::binary_op(BinOp::Add(Sort::Int), int(offset), tail_size);
            round_up(size, layout.align.abi.bytes())
        }
        _ => return Ok(None),
    };
    Ok(Some(body))
}

/// Same cases as [`meta_sized_size_of_val`]: `Sized::align_of()`, `E::align_of()`, `1`, and the
/// alignment of the struct, respectively.
fn meta_sized_align_of_val(cx: &BodyCx, alias_reft: &AliasReft) -> QueryResult<Option<Expr>> {
    let self_ty = cx.self_ty(alias_reft);
    if self_ty.is_sized(cx.tcx(), cx.typing_env) {
        return cx
            .alias(LangItem::Sized, sym::align_of, self_ty, List::empty())
            .map(Some);
    }
    let body = match self_ty.kind() {
        rustc_ty::Slice(elem) => cx.alias(LangItem::Sized, sym::align_of, *elem, List::empty())?,
        rustc_ty::Str => int(1),
        rustc_ty::Adt(..) | rustc_ty::Tuple(..) => {
            let Some(layout) = dst_layout(cx, self_ty) else { return Ok(None) };
            int(layout.align.abi.bytes())
        }
        _ => return Ok(None),
    };
    Ok(Some(body))
}

/// The layout of a struct or tuple whose tail is a slice or `str`. The offset of a `dyn Trait` tail
/// depends on its dynamic alignment, so we only handle slice and `str` tails, for which the layout
/// of the prefix is static.
fn dst_layout<'tcx>(
    cx: &BodyCx<'_, 'tcx>,
    ty: rustc_ty::Ty<'tcx>,
) -> Option<rustc_abi::TyAndLayout<'tcx, rustc_ty::Ty<'tcx>>> {
    let tail = cx.tcx().struct_tail_for_codegen(ty, cx.typing_env);
    if !matches!(tail.kind(), rustc_ty::Slice(_) | rustc_ty::Str) {
        return None;
    }
    cx.layout(ty)
}

fn int(n: u64) -> Expr {
    Expr::constant(rty::Constant::from(n))
}

/// `round_up(e, align)` for a constant `align`, i.e., `(e + align - 1) / align * align`.
fn round_up(e: Expr, align: u64) -> Expr {
    if align == 1 {
        return e;
    }
    let bumped = Expr::binary_op(
        BinOp::Sub(Sort::Int),
        Expr::binary_op(BinOp::Add(Sort::Int), e, int(align)),
        int(1),
    );
    Expr::binary_op(
        BinOp::Mul(Sort::Int),
        Expr::binary_op(BinOp::Div(Sort::Int), bumped, int(align)),
        int(align),
    )
}
