//! Diagnostic-only abstraction of signatures over a Rust-derived template.
use std::{
    collections::hash_map::DefaultHasher,
    fs::OpenOptions,
    hash::{Hash, Hasher},
    io::Write,
};

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use serde_json::json;

static TRACKING_STATUS: std::sync::LazyLock<
    std::sync::Mutex<std::collections::BTreeMap<String, String>>,
> = std::sync::LazyLock::new(Default::default);

pub fn tracking_status(wkvid: &str) -> String {
    TRACKING_STATUS
        .lock()
        .unwrap()
        .get(wkvid)
        .cloned()
        .unwrap_or_else(|| "missing_signature_record".into())
}

use super::{
    fold::{TypeFolder, TypeSuperFoldable},
    refining::{Refine, Refiner},
    *,
};

struct Matcher {
    next: usize,
    bindings: FxHashMap<Expr, Expr>,
    slots: Vec<(WKVar, usize)>,
    predicates: Vec<(Expr, usize)>,
    parents: Vec<usize>,
    regions: Vec<usize>,
    group: usize,
}

impl Matcher {
    fn open<T: TypeFoldable>(&mut self, binder: &Binder<T>) -> T {
        binder.replace_bound_vars(
            |_| Region::ReErased,
            |_, _, _| {
                let e = Expr::fvar(Name::from_usize(self.next));
                self.next += 1;
                e
            },
        )
    }

    fn scoped(&mut self, f: impl FnOnce(&mut Self) -> Result<(), String>) -> Result<(), String> {
        let parent = self.group;
        self.group = self.parents.len();
        self.parents.push(parent);
        self.regions.push(self.regions[parent]);
        let result = f(self);
        self.group = parent;
        result
    }

    fn pred(&mut self, pred: &Expr, skeleton: bool) {
        if skeleton {
            if let ExprKind::WKVar(w) = pred.kind() {
                self.slots.push((w.clone(), self.group));
            } else if let ExprKind::BinaryOp(BinOp::And, a, b) = pred.kind() {
                self.pred(a, true);
                self.pred(b, true);
            }
        } else if !pred.is_trivially_true() {
            self.predicates.push((pred.clone(), self.group));
        }
    }

    fn index(&mut self, a: &Expr, b: &Expr) {
        // A Rust-derived ADT index is one product variable; annotations often
        // spell out its fields as a constructor. Align fields with projections.
        if let ExprKind::Ctor(Ctor::Struct(def_id), fields) = b.kind()
            && !matches!(a.kind(), ExprKind::Ctor(..))
        {
            for (field, b) in fields.iter().enumerate() {
                self.index(
                    &Expr::field_proj(a, FieldProj::Adt { def_id: *def_id, field: field as u32 }),
                    b,
                );
            }
            return;
        }
        match (a.kind(), b.kind()) {
            (ExprKind::Tuple(a), ExprKind::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b) {
                    self.index(a, b);
                }
                return;
            }
            (ExprKind::Ctor(ac, a), ExprKind::Ctor(bc, b)) if ac == bc && a.len() == b.len() => {
                for (a, b) in a.iter().zip(b) {
                    self.index(a, b);
                }
                return;
            }
            _ => {}
        }
        if matches!(b.kind(), ExprKind::Var(Var::Free(_) | Var::EarlyParam(_)))
            && !self.bindings.contains_key(b)
        {
            self.bindings.insert(b.clone(), a.clone());
        } else if a != b {
            self.predicates.push((Expr::eq(a, b), self.group));
        }
    }

    fn sig(&mut self, a: &PolyFnSig, b: &PolyFnSig) -> Result<(), String> {
        let a = self.open(a);
        let b = self.open(b);
        if a.inputs.len() != b.inputs.len() {
            return Err("input count".into());
        }
        if a.abi != b.abi || a.safety != b.safety {
            return Err("ABI or safety differs".into());
        }
        for p in &a.requires {
            self.pred(p, true);
        }
        for p in &b.requires {
            self.pred(p, false);
        }
        for (a, b) in a.inputs.iter().zip(&b.inputs) {
            self.ty(a, b)?;
        }
        self.scoped(|this| {
            this.regions[this.group] = this.group;
            let a = this.open(&a.output);
            let b = this.open(&b.output);
            for p in &a.ensures {
                if let Ensures::Pred(p) = p {
                    this.pred(p, true);
                }
            }
            for p in &b.ensures {
                if let Ensures::Pred(p) = p {
                    this.pred(p, false);
                }
            }
            this.ty(&a.ret, &b.ret)?;
            let at = a
                .ensures
                .iter()
                .filter_map(|e| if let Ensures::Type(p, t) = e { Some((p, t)) } else { None })
                .collect::<Vec<_>>();
            let bt = b
                .ensures
                .iter()
                .filter_map(|e| if let Ensures::Type(p, t) = e { Some((p, t)) } else { None })
                .collect::<Vec<_>>();
            if at.len() != bt.len() {
                return Err("typed ensures count".into());
            }
            for ((ap, a), (bp, b)) in at.into_iter().zip(bt) {
                this.bindings.insert(bp.to_expr(), ap.to_expr());
                this.ty(a, b)?;
            }
            Ok(())
        })
    }

    fn ty(&mut self, a: &Ty, b: &Ty) -> Result<(), String> {
        match (a.kind(), b.kind()) {
            (TyKind::Exists(a), _) => {
                self.scoped(|this| {
                    let a = this.open(a);
                    this.ty(&a, b)
                })
            }
            (_, TyKind::Exists(b)) => {
                let b = self.open(b);
                self.ty(a, &b)
            }
            (TyKind::Constr(p, a), _) => {
                self.pred(p, true);
                self.ty(a, b)
            }
            (_, TyKind::Constr(p, b)) => {
                self.pred(p, false);
                self.ty(a, b)
            }
            (TyKind::Indexed(a, ai), TyKind::Indexed(b, bi)) => {
                self.index(ai, bi);
                self.bty(a, b)
            }
            (TyKind::StrgRef(_, ap, a), TyKind::StrgRef(_, bp, b)) => {
                self.bindings.insert(bp.to_expr(), ap.to_expr());
                self.ty(a, b)
            }
            _ if a == b => Ok(()),
            _ => Err(format!("type shape: {a:?} versus {b:?}")),
        }
    }

    fn args(&mut self, a: &[GenericArg], b: &[GenericArg]) -> Result<(), String> {
        if a.len() != b.len() {
            return Err("generic argument count".into());
        }
        for (a, b) in a.iter().zip(b) {
            match (a, b) {
                (GenericArg::Ty(a), GenericArg::Ty(b)) => self.ty(a, b)?,
                (GenericArg::Base(a), GenericArg::Base(b)) => {
                    self.scoped(|this| {
                        this.regions[this.group] = this.group;
                        let a = this.open(a);
                        let b = this.open(b);
                        this.pred(&a.pred, true);
                        this.pred(&b.pred, false);
                        this.index(&a.idx, &b.idx);
                        this.bty(&a.bty, &b.bty)
                    })?
                }
                (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => {}
                _ if a == b => {}
                _ => return Err("generic argument shape".into()),
            }
        }
        Ok(())
    }

    fn bty(&mut self, a: &BaseTy, b: &BaseTy) -> Result<(), String> {
        match (a, b) {
            (BaseTy::Adt(a, aa), BaseTy::Adt(b, ba)) if a.did() == b.did() => self.args(aa, ba),
            (BaseTy::Ref(_, a, am), BaseTy::Ref(_, b, bm))
            | (BaseTy::RawPtr(a, am), BaseTy::RawPtr(b, bm))
                if am == bm =>
            {
                self.ty(a, b)
            }
            (BaseTy::Slice(a), BaseTy::Slice(b)) => self.ty(a, b),
            (BaseTy::Array(a, al), BaseTy::Array(b, bl)) if al == bl => self.ty(a, b),
            (BaseTy::Tuple(a), BaseTy::Tuple(b)) if a.len() == b.len() => {
                for (a, b) in a.iter().zip(b) {
                    self.ty(a, b)?;
                }
                Ok(())
            }
            (BaseTy::FnPtr(a), BaseTy::FnPtr(b)) => self.scoped(|this| this.sig(a, b)),
            (BaseTy::Alias(a), BaseTy::Alias(b))
                if a.kind == b.kind && a.refine_args == b.refine_args =>
            {
                self.args(&a.args, &b.args)
            }
            _ if a == b => Ok(()),
            _ => Err(format!("base type shape: {a:?} versus {b:?}")),
        }
    }
}

struct Replace<'a>(&'a FxHashMap<Expr, Expr>);
impl TypeFolder for Replace<'_> {
    fn fold_expr(&mut self, e: &Expr) -> Expr {
        self.0
            .get(e)
            .cloned()
            .unwrap_or_else(|| e.super_fold_with(self))
    }
}

struct Abstract<'a> {
    args: &'a [Expr],
    depth: u32,
    failed: bool,
}
impl TypeFolder for Abstract<'_> {
    fn enter_binder(&mut self, _: &BoundVariableKinds) {
        self.depth += 1;
    }
    fn exit_binder(&mut self) {
        self.depth -= 1;
    }
    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if let Some(i) = self.args.iter().position(|a| a == e) {
            Expr::bvar(
                INNERMOST.shifted_in(self.depth),
                BoundVar::from_usize(i),
                BoundReftKind::Anon,
            )
        } else {
            if matches!(e.kind(), ExprKind::Var(Var::Free(_) | Var::EarlyParam(_))) {
                self.failed = true;
            }
            e.super_fold_with(self)
        }
    }
}

struct Strip;
impl TypeFolder for Strip {
    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if matches!(e.kind(), ExprKind::WKVar(_)) {
            Expr::tt()
        } else {
            e.erase_metadata().super_fold_with(self)
        }
    }
    fn fold_region(&mut self, _: &Region) -> Region {
        Region::ReErased
    }
}

struct EraseRegions;
impl TypeFolder for EraseRegions {
    fn fold_region(&mut self, _: &Region) -> Region {
        Region::ReErased
    }
}

/// Tracking IDs use a disjoint namespace from suggestion wkvars and carry no
/// arguments: only their provenance matters, and they are erased before solving.
pub fn is_tracking(w: &WKVar) -> bool {
    w.wkvid.id.as_u32() >= (1 << 31)
}

pub fn erase_tracking<T: TypeFoldable>(value: &T) -> T {
    struct Erase;
    impl TypeFolder for Erase {
        fn fold_ty(&mut self, ty: &Ty) -> Ty {
            let ty = ty.super_fold_with(self);
            if let TyKind::Constr(p, t) = ty.kind()
                && p.is_trivially_true()
            {
                t.clone()
            } else {
                ty
            }
        }
        fn fold_expr(&mut self, e: &Expr) -> Expr {
            if let ExprKind::WKVar(w) = e.kind()
                && is_tracking(w)
            {
                Expr::tt()
            } else {
                e.super_fold_with(self)
            }
        }
    }
    value.fold_with(&mut Erase)
}

/// A structural address ignores existential/constraint wrappers and indices.
/// Those are precisely the parts that annotations can change.
#[derive(Default)]
struct Sites {
    next: usize,
    site: String,
    slots: Vec<(u32, String)>,
    inject: FxHashMap<String, Vec<u32>>,
    inserted: Vec<u32>,
    def_id: Option<DefId>,
    shape: Vec<String>,
}
impl Sites {
    fn markers(&mut self, site: &str) -> Vec<Expr> {
        self.inject
            .get(site)
            .into_iter()
            .flatten()
            .map(|id| {
                self.inserted.push(*id);
                Expr::wkvar(WKVar {
                    wkvid: WKVid::new(self.def_id.unwrap(), KVid::from_u32(*id | (1 << 31))),
                    self_args: 0,
                    args: List::empty(),
                })
            })
            .collect()
    }
}
impl TypeFolder for Sites {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        let parent = self.site.clone();
        self.site = format!("type:{}", self.next);
        let site = self.site.clone();
        let structural = !matches!(ty.kind(), TyKind::Exists(_) | TyKind::Constr(..));
        if structural {
            self.shape.push(match ty.kind() {
                TyKind::Indexed(bty, _) => {
                    match bty {
                        BaseTy::Adt(def, _) => format!("adt:{:?}", def.did()),
                        BaseTy::Ref(_, _, m) => format!("ref:{m:?}"),
                        BaseTy::Tuple(ts) => format!("tuple:{}", ts.len()),
                        BaseTy::Slice(_) => "slice".into(),
                        _ => format!("{:?}", std::mem::discriminant(bty)),
                    }
                }
                TyKind::StrgRef(..) => "strg".into(),
                _ => format!("{:?}", std::mem::discriminant(ty.kind())),
            });
            self.next += 1;
        }
        let ty = ty.super_fold_with(self);
        let ty = if structural {
            self.markers(&site)
                .into_iter()
                .fold(ty, |ty, p| Ty::constr(p, ty))
        } else {
            ty
        };
        self.site = parent;
        ty
    }
    fn fold_subset_ty(&mut self, ty: &SubsetTy) -> SubsetTy {
        let parent = self.site.clone();
        self.site = format!("base:{}", self.next);
        self.next += 1;
        self.shape.push("base".into());
        let site = self.site.clone();
        let mut ty = ty.super_fold_with(self);
        for marker in self.markers(&site) {
            ty = ty.strengthen(marker);
        }
        self.site = parent;
        ty
    }
    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if let ExprKind::WKVar(w) = e.kind() {
            self.slots.push((w.wkvid.id.as_u32(), self.site.clone()));
        }
        // Do not count types in expressions as signature type positions.
        e.clone()
    }
}

fn sites(sig: &PolyFnSig) -> Sites {
    let mut folder = Sites::default();
    let body = sig.skip_binder_ref();
    for p in &body.requires {
        folder.site = "requires".into();
        folder.fold_expr(p);
    }
    for input in &body.inputs {
        folder.fold_ty(input);
    }
    folder.fold_ty(&body.output.skip_binder_ref().ret);
    for e in &body.output.skip_binder_ref().ensures {
        match e {
            Ensures::Pred(p) => {
                folder.site = "ensures".into();
                folder.fold_expr(p);
            }
            Ensures::Type(_, ty) => {
                folder.fold_ty(ty);
            }
        }
    }
    folder
}

pub(crate) fn log_and_track(genv: GlobalEnv, def_id: DefId, sig: &PolyFnSig) -> PolyFnSig {
    let pretty = |sig: &PolyFnSig| {
        format!("{:?}", crate::pretty::with_cx!(&PrettyCx::default(genv), &EarlyBinder(sig)))
    };
    let annotated = sig.fold_with(&mut Strip);
    let mut record = json!({"schema_version": 1, "function": genv.tcx().def_path_str(def_id), "annotated": pretty(&annotated)});
    let mut tracking_sites = vec![];
    let mut skeleton_shape = vec![];
    let result = (|| -> Result<(), String> {
        let raw = genv
            .lower_fn_sig(def_id)
            .map_err(|e| format!("lower signature: {e:?}"))?
            .skip_binder();
        let refiner =
            Refiner::default_for_item(genv, def_id).map_err(|e| format!("refiner: {e:?}"))?;
        let default = raw
            .refine(&refiner)
            .map_err(|e| format!("default refinement: {e:?}"))?
            .hoist_input_binders();
        let default = auto_strong(genv, def_id, default).hoist_input_binders();
        let (skeleton, info) = default
            .with_weak_kvars(genv, def_id, true)
            .map_err(|e| format!("wkvars: {e:?}"))?;
        let skeleton = skeleton.fold_with(&mut EraseRegions);
        let addresses = sites(&skeleton);
        tracking_sites = addresses.slots;
        skeleton_shape = addresses.shape;
        let text = pretty(&skeleton);
        let mut hash = DefaultHasher::new();
        text.hash(&mut hash);
        record["skeleton"] = text.into();
        record["skeleton_fingerprint"] = format!("{:016x}", hash.finish()).into();
        // Apply the same existing auto-strong transformation to lifted annotations.
        let annotated = auto_strong(
            genv,
            def_id,
            annotated.clone().map(|mut sig| {
                sig.lifted = true;
                sig
            }),
        )
        .hoist_input_binders();
        let mut matcher = Matcher {
            next: 0,
            bindings: FxHashMap::default(),
            slots: vec![],
            predicates: vec![],
            parents: vec![0],
            regions: vec![0],
            group: 0,
        };
        matcher.sig(&skeleton, &annotated)?;
        let mut solutions: FxHashMap<WKVid, Vec<Expr>> = FxHashMap::default();
        for (pred, group) in &matcher.predicates {
            let origin = *group;
            let mut group = origin;
            let pred = pred.fold_with(&mut Replace(&matcher.bindings));
            let mut found = false;
            loop {
                for (slot, sg) in &matcher.slots {
                    if *sg != group {
                        continue;
                    }
                    let mut folder = Abstract { args: &slot.args, depth: 0, failed: false };
                    let body = pred.fold_with(&mut folder);
                    if !folder.failed {
                        solutions.entry(slot.wkvid.clone()).or_default().push(body);
                        found = true;
                        break;
                    }
                }
                if found || group == 0 {
                    break;
                }
                let parent = matcher.parents[group];
                if matcher.regions[parent] != matcher.regions[origin] {
                    break;
                }
                group = parent;
            }
            if !found {
                // Mutable-reference input indices can remain under existentials.
                // Try a nested slot in the same input/output/generic region.
                for (slot, sg) in &matcher.slots {
                    if matcher.regions[*sg] != matcher.regions[origin] {
                        continue;
                    }
                    let mut folder = Abstract { args: &slot.args, depth: 0, failed: false };
                    let body = pred.fold_with(&mut folder);
                    if !folder.failed {
                        solutions.entry(slot.wkvid.clone()).or_default().push(body);
                        found = true;
                        break;
                    }
                }
            }
            if !found {
                // TODO: as_mut_slice needs an outer anchor n for an index x kept
                // existential inside &mut. Skeleton hoisting should retain x and
                // introduce forall n, letting W(x,n) be true or x == n; actually
                // hoisting x would incorrectly freeze an otherwise mutable index.
                // collect_rvec also needs abstract/alias-sort indices passed to
                // diagnostic wkvars (the solver-facing suggestion filter skips them).
                return Err(format!("no in-scope wkvar for {pred:?}"));
            }
        }
        let mut substitutions = FxHashMap::default();
        let mut entries = vec![];
        for (slot, _) in &matcher.slots {
            let sorts = &info[&slot.wkvid.id.as_u32()].sorts;
            let body = Expr::and_from_iter(solutions.remove(&slot.wkvid).unwrap_or_default());
            let solution = Binder::bind_with_sorts(body, sorts);
            entries.push(json!({
                "id": slot.wkvid.id.as_u32(),
                "self_args": slot.self_args,
                "parameter_sorts": sorts.iter().map(|sort| format!("{:?}", crate::pretty::with_cx!(&PrettyCx::default(genv), sort))).collect::<Vec<_>>(),
                "solution": format!("{:?}", crate::pretty::with_cx!(&PrettyCx::default(genv), &solution)),
            }));
            substitutions.insert(slot.wkvid.clone(), solution);
        }
        struct Subst(FxHashMap<WKVid, Binder<Expr>>);
        impl TypeFolder for Subst {
            fn fold_expr(&mut self, e: &Expr) -> Expr {
                if let ExprKind::WKVar(w) = e.kind() {
                    self.0[&w.wkvid].replace_bound_refts(&w.args)
                } else {
                    e.super_fold_with(self)
                }
            }
        }
        let reconstructed = skeleton.fold_with(&mut Subst(substitutions));
        record["instantiations"] = entries.into();
        record["reconstructed"] = pretty(&reconstructed).into();
        record["structurally_equal"] = (reconstructed == annotated).into();
        Ok(())
    })();
    record["status"] = if result.is_ok() { "matched" } else { "failed" }.into();
    if let Err(reason) = result {
        record["reason"] = reason.into();
    }
    // Add provenance to the annotated signature, preserving its predicates,
    // indices, binders, regions, and existing suggestion wkvars.
    let mut folder = Sites { def_id: Some(def_id), ..Sites::default() };
    for (id, site) in &tracking_sites {
        folder.inject.entry(site.clone()).or_default().push(*id);
    }
    let tracked = sig.clone().map(|mut body| {
        let mut requires = body.requires.to_vec();
        requires.extend(folder.markers("requires"));
        body.requires = requires.into();
        body.inputs = body.inputs.iter().map(|ty| folder.fold_ty(ty)).collect();
        body.output = body.output.map(|mut out| {
            out.ret = folder.fold_ty(&out.ret);
            let mut ensures = out
                .ensures
                .iter()
                .map(|e| {
                    match e {
                        Ensures::Type(p, t) => Ensures::Type(p.clone(), folder.fold_ty(t)),
                        _ => e.clone(),
                    }
                })
                .collect::<Vec<_>>();
            ensures.extend(folder.markers("ensures").into_iter().map(Ensures::Pred));
            out.ensures = ensures.into();
            out
        });
        body
    });
    let mut inserted = folder.inserted.clone();
    inserted.sort();
    let mut expected = tracking_sites.iter().map(|(id, _)| *id).collect::<Vec<_>>();
    expected.sort();
    let complete = inserted == expected && folder.shape == skeleton_shape;
    record["tracking_alignment"] = json!({"complete":complete,"slots":tracking_sites.iter().map(|(id,site)| json!({"wkvid":format!("{}::wk{}",genv.tcx().def_path_str(def_id),id),"site":site,"inserted":inserted.contains(id),"matching_status":record["status"]})).collect::<Vec<_>>()});
    // Type-site numbering is only a candidate alignment. Require matching and
    // complete coverage, and verify that erasure preserves the original type.
    struct Clean;
    impl TypeFolder for Clean {
        fn fold_ty(&mut self, ty: &Ty) -> Ty {
            let ty = ty.super_fold_with(self);
            if let TyKind::Constr(p, t) = ty.kind()
                && p.is_trivially_true()
            {
                t.clone()
            } else {
                ty
            }
        }
    }
    let clean_sig = |sig: &PolyFnSig| {
        sig.fold_with(&mut Clean).map(|mut body| {
            body.requires = body
                .requires
                .iter()
                .filter(|p| !p.is_trivially_true())
                .cloned()
                .collect();
            body.output = body.output.map(|mut out| {
                out.ensures = out
                    .ensures
                    .iter()
                    .filter(|e| !matches!(e,Ensures::Pred(p) if p.is_trivially_true()))
                    .cloned()
                    .collect();
                out
            });
            body
        })
    };
    let erasure_equal = clean_sig(&erase_tracking(&tracked)) == clean_sig(sig);
    record["tracking_alignment"]["erasure_equal"] = erasure_equal.into();
    record["tracking_alignment"]["emitted"] = (complete && erasure_equal).into();
    record["tracking_alignment"]["usable"] =
        (complete && erasure_equal && record["status"] == "matched").into();
    if record["status"] != "matched" {
        record["unmatched_wkvids"] = tracking_sites
            .iter()
            .map(|(id, _)| format!("{}::wk{id}", genv.tcx().def_path_str(def_id)))
            .collect::<Vec<_>>()
            .into();
    }
    record["wkvar_map"] = record
        .get("instantiations")
        .and_then(|v| v.as_array())
        .map(|entries| {
            entries
                .iter()
                .map(|entry| {
                    (
                        format!("{}::wk{}", genv.tcx().def_path_str(def_id), entry["id"]),
                        entry["solution"].clone(),
                    )
                })
                .collect::<serde_json::Map<_, _>>()
        })
        .unwrap_or_default()
        .into();
    for (id, _) in &tracking_sites {
        let key = format!("{}::wk{id}", genv.tcx().def_path_str(def_id));
        if record["wkvar_map"].get(&key).is_none() {
            record["wkvar_map"][&key] = serde_json::Value::Null;
        }
        let status = if record["status"] != "matched" {
            "skeleton_matching_failed"
        } else if !complete || !erasure_equal {
            "alignment_failed"
        } else {
            "aligned"
        };
        TRACKING_STATUS.lock().unwrap().insert(key, status.into());
    }
    let write = || -> std::io::Result<()> {
        std::fs::create_dir_all(flux_config::log_dir())?;
        let path = flux_config::log_dir().join(format!(
            "{}-vc-skeletons.jsonl",
            genv.tcx().crate_name(rustc_hir::def_id::LOCAL_CRATE)
        ));
        let mut file = OpenOptions::new().create(true).append(true).open(path)?;
        serde_json::to_writer(&mut file, &record)?;
        writeln!(file)
    };
    if let Err(error) = write() {
        eprintln!("could not log VC skeleton: {error}");
    }
    // Never propagate guessed addresses or a signature that fails the erasure
    // sanity check. The signature record still lists every unavailable slot.
    if complete && erasure_equal { tracked } else { sig.clone() }
}
