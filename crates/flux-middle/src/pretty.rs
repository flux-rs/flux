use std::{cell::RefCell, fmt};

use flux_arc_interner::{Internable, Interned};
use flux_common::index::IndexGen;
use flux_config as config;
use rustc_data_structures::unord::UnordMap;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Pos, Span};
use rustc_target::abi::FieldIdx;
use rustc_type_ir::{BoundVar, DebruijnIndex, INNERMOST};
use serde::Serialize;

#[macro_export]
macro_rules! _with_cx {
    ($cx:expr, $e:expr) => {
        $crate::pretty::WithCx::new($cx, $e)
    };
}
pub use crate::_with_cx as with_cx;
use crate::def_id::{FluxDefId, FluxLocalDefId};

#[macro_export]
macro_rules! _format_args_cx {
    ($cx:ident, $fmt:literal, $($args:tt)*) => {
        $crate::_format_args_cx!(@go ($cx, $fmt; $($args)*) -> ())
    };
    ($cx:expr, $fmt:literal) => {
        format_args!($fmt)
    };
    (@go ($cx:ident, $fmt:literal; ^$head:expr, $($tail:tt)*) -> ($($accum:tt)*)) => {
        $crate::_format_args_cx!(@go ($cx, $fmt; $($tail)*) -> ($($accum)* $head,))
    };
    (@go ($cx:ident, $fmt:literal; $head:expr, $($tail:tt)*) -> ($($accum:tt)*)) => {
        $crate::_format_args_cx!(@go ($cx, $fmt; $($tail)*) -> ($($accum)* $crate::pretty::with_cx!($cx, $head),))
    };
    (@go ($cx:ident, $fmt:literal; ^$head:expr) -> ($($accum:tt)*)) => {
        $crate::_format_args_cx!(@as_expr format_args!($fmt, $($accum)* $head,))
    };
    (@go ($cx:ident, $fmt:literal; $head:expr) -> ($($accum:tt)*)) => {
        $crate::_format_args_cx!(@as_expr format_args!($fmt, $($accum)* $crate::pretty::with_cx!($cx, $head),))
    };
    (@as_expr $e:expr) => { $e };
}
pub use crate::_format_args_cx as format_args_cx;

#[macro_export]
macro_rules! _format_cx {
    ($($arg:tt)*) => {
        std::fmt::format($crate::_format_args_cx!($($arg)*))
    }
}
pub use crate::_format_cx as format_cx;

#[macro_export]
macro_rules! _w {
    ($cx:expr, $f:expr, $fmt:literal, $($args:tt)*) => {{
        #[allow(unused_variables)]
        let cx = $cx;
        $f.write_fmt($crate::_format_args_cx!(cx, $fmt, $($args)*))
    }};
    ($cx:expr, $f:expr, $fmt:literal) => {
        $f.write_fmt($crate::_format_args_cx!($cx, $fmt))
    };
}
pub use crate::_w as w;

#[macro_export]
macro_rules! _join {
    ($sep:expr, $iter:expr) => {
        $crate::pretty::Join::new($sep, $iter)
    };
}
pub use crate::_join as join;

#[macro_export]
macro_rules! _parens {
    ($val:expr, $parenthesize:expr) => {
        $crate::pretty::Parens::new(&$val, $parenthesize)
    };
}
pub use crate::_parens as parens;

#[macro_export]
macro_rules! _impl_debug_with_default_cx {
    ($($ty:ty $(=> $key:literal)?),* $(,)?) => {$(
        impl std::fmt::Debug for $ty  {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                #[allow(unused_mut, unused_assignments)]
                let mut key = None;
                $(
                    key = Some($key);
                )?
                $crate::pretty::pprint_with_default_cx(f, self, key)
            }
        }
    )*};
}

pub fn pprint_with_default_cx<T: Pretty>(
    f: &mut std::fmt::Formatter<'_>,
    t: &T,
    cfg_key: Option<&'static str>,
) -> std::fmt::Result {
    rustc_middle::ty::tls::with(|tcx| {
        #[allow(unused_mut)]
        let mut cx = <T>::default_cx(tcx);

        if let Some(pprint) = flux_config::CONFIG_FILE
            .get("dev")
            .and_then(|dev| dev.get("pprint"))
        {
            if let Some(opts) = pprint.get("default") {
                cx.merge(opts);
            }

            if let Some(key) = cfg_key
                && let Some(opts) = pprint.get(key)
            {
                cx.merge(opts);
            }
        }

        if let Some(key) = cfg_key
            && let Some(opts) = flux_config::CONFIG_FILE
                .get("dev")
                .and_then(|dev| dev.get("pprint"))
                .and_then(|pprint| pprint.get(key))
        {
            cx.merge(opts);
        }
        Pretty::fmt(t, &cx, f)
    })
}

pub use crate::_impl_debug_with_default_cx as impl_debug_with_default_cx;
use crate::{
    global_env::GlobalEnv,
    rty::{AdtSortDef, BoundReft, BoundReftKind, BoundVariableKind},
};

#[derive(Copy, Clone)]
pub enum KVarArgs {
    All,
    SelfOnly,
    Hide,
}

#[derive(Clone, Copy)]
pub enum GenvOrTcx<'genv, 'tcx> {
    Genv(GlobalEnv<'genv, 'tcx>),
    Tcx(TyCtxt<'tcx>),
}

impl<'genv, 'tcx> GenvOrTcx<'genv, 'tcx> {
    fn tcx(self) -> TyCtxt<'tcx> {
        match self {
            GenvOrTcx::Genv(genv) => genv.tcx(),
            GenvOrTcx::Tcx(tcx) => tcx,
        }
    }

    fn genv(self) -> Option<GlobalEnv<'genv, 'tcx>> {
        match self {
            GenvOrTcx::Genv(genv) => Some(genv),
            GenvOrTcx::Tcx(_) => None,
        }
    }
}

impl<'tcx> From<TyCtxt<'tcx>> for GenvOrTcx<'_, 'tcx> {
    fn from(v: TyCtxt<'tcx>) -> Self {
        Self::Tcx(v)
    }
}

impl<'genv, 'tcx> From<GlobalEnv<'genv, 'tcx>> for GenvOrTcx<'genv, 'tcx> {
    fn from(v: GlobalEnv<'genv, 'tcx>) -> Self {
        Self::Genv(v)
    }
}

pub struct PrettyCx<'genv, 'tcx> {
    pub cx: GenvOrTcx<'genv, 'tcx>,
    pub kvar_args: KVarArgs,
    pub fully_qualified_paths: bool,
    pub simplify_exprs: bool,
    pub tags: bool,
    pub bindings_chain: bool,
    pub preds_chain: bool,
    pub full_spans: bool,
    pub hide_uninit: bool,
    pub hide_refinements: bool,
    pub hide_regions: bool,
    pub hide_sorts: bool,
    env: BoundVarEnv,
}

macro_rules! set_opts {
    ($cx:expr, $opts:expr, [$($opt:ident),+ $(,)?]) => {
        $(
        if let Some(val) = $opts.get(stringify!($opt)).and_then(|v| FromOpt::from_opt(v)) {
            $cx.$opt = val;
        }
        )+
    };
}

impl<'genv, 'tcx> PrettyCx<'genv, 'tcx> {
    pub fn default(cx: impl Into<GenvOrTcx<'genv, 'tcx>>) -> Self {
        PrettyCx {
            cx: cx.into(),
            kvar_args: KVarArgs::SelfOnly,
            fully_qualified_paths: false,
            simplify_exprs: true,
            tags: true,
            bindings_chain: true,
            preds_chain: true,
            full_spans: false,
            hide_uninit: true,
            hide_refinements: false,
            hide_regions: false,
            hide_sorts: true,
            env: BoundVarEnv::default(),
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.cx.tcx()
    }

    pub fn genv(&self) -> Option<GlobalEnv<'genv, 'tcx>> {
        self.cx.genv()
    }

    pub fn adt_sort_def_of(&self, def_id: DefId) -> Option<AdtSortDef> {
        self.genv()
            .and_then(|genv| genv.adt_sort_def_of(def_id).ok())
    }

    pub fn merge(&mut self, opts: &config::Value) {
        set_opts!(self, opts, [
            kvar_args,
            fully_qualified_paths,
            simplify_exprs,
            tags,
            bindings_chain,
            preds_chain,
            full_spans,
            hide_uninit,
            hide_refinements,
            hide_regions,
            hide_sorts,
        ]);
    }

    pub fn with_bound_vars<R>(&self, vars: &[BoundVariableKind], f: impl FnOnce() -> R) -> R {
        self.env.push_layer(vars);
        let r = f();
        self.env.pop_layer();
        r
    }

    pub fn fmt_bound_vars(
        &self,
        print_infer_mode: bool,
        left: &str,
        vars: &[BoundVariableKind],
        right: &str,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        w!(self, f, "{left}")?;
        for (i, var) in vars.iter().enumerate() {
            if i > 0 {
                w!(self, f, ", ")?;
            }
            match var {
                BoundVariableKind::Region(re) => w!(self, f, "{:?}", re)?,
                BoundVariableKind::Refine(sort, mode, BoundReftKind::Named(name)) => {
                    if print_infer_mode {
                        w!(self, f, "{}", ^mode.prefix_str())?;
                    }
                    w!(self, f, "{}", ^name)?;
                    if !self.hide_sorts {
                        w!(self, f, ": {:?}", sort)?;
                    }
                }
                BoundVariableKind::Refine(sort, mode, BoundReftKind::Annon) => {
                    if print_infer_mode {
                        w!(self, f, "{}", ^mode.prefix_str())?;
                    }
                    if let Some(name) = self.env.lookup(INNERMOST, BoundVar::from_usize(i)) {
                        w!(self, f, "{:?}", ^name)?;
                    } else {
                        w!(self, f, "_")?;
                    }
                    if !self.hide_sorts {
                        w!(self, f, ": {:?}", sort)?;
                    }
                }
            }
        }
        w!(self, f, "{right}")
    }

    pub fn fmt_bound_reft(
        &self,
        debruijn: DebruijnIndex,
        breft: BoundReft,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match breft.kind {
            BoundReftKind::Annon => {
                if let Some(name) = self.env.lookup(debruijn, breft.var) {
                    w!(self, f, "{name:?}")
                } else {
                    w!(self, f, "⭡{}/#{:?}", ^debruijn.as_usize(), ^breft.var)
                }
            }
            BoundReftKind::Named(name) => w!(self, f, "{name}"),
        }
    }

    pub fn kvar_args(self, kvar_args: KVarArgs) -> Self {
        Self { kvar_args, ..self }
    }

    pub fn fully_qualified_paths(self, b: bool) -> Self {
        Self { fully_qualified_paths: b, ..self }
    }

    pub fn hide_regions(self, b: bool) -> Self {
        Self { hide_regions: b, ..self }
    }

    pub fn hide_sorts(self, b: bool) -> Self {
        Self { hide_sorts: b, ..self }
    }

    pub fn hide_refinements(self, b: bool) -> Self {
        Self { hide_refinements: b, ..self }
    }
}

newtype_index! {
    /// Name used during pretty printing to format anonymous bound variables
    #[debug_format = "b{}"]
    struct BoundVarName {}
}

#[derive(Default)]
struct BoundVarEnv {
    name_gen: IndexGen<BoundVarName>,
    layers: RefCell<Vec<UnordMap<BoundVar, BoundVarName>>>,
}

impl BoundVarEnv {
    fn lookup(&self, debruijn: DebruijnIndex, var: BoundVar) -> Option<BoundVarName> {
        let layers = self.layers.borrow();
        layers
            .get(layers.len().checked_sub(debruijn.as_usize() + 1)?)?
            .get(&var)
            .copied()
    }

    fn push_layer(&self, vars: &[BoundVariableKind]) {
        let mut layer = UnordMap::default();
        for (idx, var) in vars.iter().enumerate() {
            if let BoundVariableKind::Refine(_, _, BoundReftKind::Annon) = var {
                layer.insert(BoundVar::from_usize(idx), self.name_gen.fresh());
            }
        }
        self.layers.borrow_mut().push(layer);
    }

    fn pop_layer(&self) {
        self.layers.borrow_mut().pop();
    }
}

pub struct WithCx<'a, 'genv, 'tcx, T> {
    data: T,
    cx: &'a PrettyCx<'genv, 'tcx>,
}

pub struct Join<'a, I> {
    sep: &'a str,
    iter: RefCell<Option<I>>,
}

pub struct Parens<'a, T> {
    val: &'a T,
    parenthesize: bool,
}

pub trait Pretty {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    fn default_cx(tcx: TyCtxt) -> PrettyCx {
        PrettyCx::default(tcx)
    }
}

impl Pretty for String {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<'a, I> Join<'a, I> {
    pub fn new<T: IntoIterator<IntoIter = I>>(sep: &'a str, iter: T) -> Self {
        Self { sep, iter: RefCell::new(Some(iter.into_iter())) }
    }
}

impl<'a, T> Parens<'a, T> {
    pub fn new(val: &'a T, parenthesize: bool) -> Self {
        Self { val, parenthesize }
    }
}

impl<'a, 'genv, 'tcx, T> WithCx<'a, 'genv, 'tcx, T> {
    pub fn new(cx: &'a PrettyCx<'genv, 'tcx>, data: T) -> Self {
        Self { data, cx }
    }
}

impl<T: Pretty + ?Sized> Pretty for &'_ T {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as Pretty>::fmt(self, cx, f)
    }
}

impl<T: Pretty + Internable> Pretty for Interned<T> {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as Pretty>::fmt(self, cx, f)
    }
}

impl<T, I> fmt::Debug for Join<'_, I>
where
    T: fmt::Debug,
    I: Iterator<Item = T>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some(iter) = self.iter.borrow_mut().take() else {
            panic!("Join: was already formatted once")
        };
        for (i, item) in iter.enumerate() {
            if i > 0 {
                write!(f, "{}", self.sep)?;
            }
            <T as fmt::Debug>::fmt(&item, f)?;
        }
        Ok(())
    }
}

impl<T, I> Pretty for Join<'_, I>
where
    T: Pretty,
    I: Iterator<Item = T>,
{
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some(iter) = self.iter.borrow_mut().take() else {
            panic!("Join: was already formatted once")
        };
        for (i, item) in iter.enumerate() {
            if i > 0 {
                write!(f, "{}", self.sep)?;
            }
            <T as Pretty>::fmt(&item, cx, f)?;
        }
        Ok(())
    }
}
impl<T> Pretty for Parens<'_, T>
where
    T: Pretty,
{
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.parenthesize {
            write!(f, "(")?;
        }
        <T as Pretty>::fmt(self.val, cx, f)?;
        if self.parenthesize {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<T: Pretty> fmt::Debug for WithCx<'_, '_, '_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as Pretty>::fmt(&self.data, self.cx, f)
    }
}

impl Pretty for DefId {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let path = cx.tcx().def_path(*self);
        if cx.fully_qualified_paths {
            let krate = cx.tcx().crate_name(self.krate);
            w!(cx, f, "{}{}", ^krate, ^path.to_string_no_crate_verbose())
        } else {
            w!(cx, f, "{}", ^path.data.last().unwrap())
        }
    }
}

impl Pretty for FluxDefId {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if cx.fully_qualified_paths {
            w!(cx, f, "{:?}::{}", self.parent(), ^self.name())
        } else {
            w!(cx, f, "{}", ^self.name())
        }
    }
}

impl Pretty for FluxLocalDefId {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        w!(cx, f, "{:?}", self.to_def_id())
    }
}

impl Pretty for FieldIdx {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_u32())
    }
}

impl Pretty for Span {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if cx.full_spans {
            write!(f, "{self:?}")
        } else {
            let src_map = cx.tcx().sess.source_map();
            let lo = src_map.lookup_char_pos(self.lo());
            let hi = src_map.lookup_char_pos(self.hi());
            // use rustc_span::FileName;
            // match lo.file.name {
            //     FileName::Real(ref name) => {
            //         write!(
            //             f,
            //             "{}",
            //             name.local_path_if_available()
            //                 .file_name()
            //                 .unwrap()
            //                 .to_string_lossy()
            //         )
            //     }
            //     FileName::QuoteExpansion(_) => write!(f, "<quote expansion>"),
            //     FileName::MacroExpansion(_) => write!(f, "<macro expansion>"),
            //     FileName::Anon(_) => write!(f, "<anon>"),
            //     FileName::ProcMacroSourceCode(_) => write!(f, "<proc-macro source code>"),
            //     FileName::CfgSpec(_) => write!(f, "<cfgspec>"),
            //     FileName::CliCrateAttr(_) => write!(f, "<crate attribute>"),
            //     FileName::Custom(ref s) => write!(f, "<{}>", s),
            //     FileName::DocTest(ref path, _) => write!(f, "{}", path.display()),
            //     FileName::InlineAsm(_) => write!(f, "<inline asm>"),
            // }?;
            write!(
                f,
                "{}:{}: {}:{}",
                lo.line,
                lo.col.to_usize() + 1,
                hi.line,
                hi.col.to_usize() + 1,
            )
        }
    }
}

trait FromOpt: Sized {
    fn from_opt(opt: &config::Value) -> Option<Self>;
}

impl FromOpt for bool {
    fn from_opt(opt: &config::Value) -> Option<Self> {
        opt.as_bool()
    }
}

impl FromOpt for KVarArgs {
    fn from_opt(opt: &config::Value) -> Option<Self> {
        match opt.as_str() {
            Some("self") => Some(KVarArgs::SelfOnly),
            Some("hide") => Some(KVarArgs::Hide),
            Some("all") => Some(KVarArgs::All),
            _ => None,
        }
    }
}

// -------------------------------------------------------------------------------------------------------------

#[derive(Serialize)]
pub struct NestedString {
    pub text: String,
    pub key: Option<String>,
    pub children: Option<Vec<NestedString>>,
}

pub fn debug_nested<T: Pretty>(cx: &PrettyCx, t: &T) -> Result<NestedString, fmt::Error> {
    let t = WithCx::new(cx, t);
    let text = format!("{:?}", t);
    Ok(NestedString { text, children: None, key: None })
}

pub fn float_children(children: Vec<Option<Vec<NestedString>>>) -> Option<Vec<NestedString>> {
    let mut childrens: Vec<_> = children.into_iter().flatten().collect();
    if childrens.is_empty() {
        None
    } else if childrens.len() == 1 {
        let c = childrens.pop().unwrap();
        Some(c)
    } else {
        let mut res = vec![];
        for (i, children) in childrens.into_iter().enumerate() {
            res.push(NestedString {
                text: format!("arg{}", i),
                children: Some(children),
                key: None,
            });
        }
        Some(res)
    }
}

pub trait PrettyNested {
    fn fmt_nested(&self, cx: &PrettyCx) -> Result<NestedString, fmt::Error>;

    fn nested_string(&self, cx: &PrettyCx) -> String {
        let res = self.fmt_nested(cx).unwrap();
        serde_json::to_string(&res).unwrap()
    }
}
