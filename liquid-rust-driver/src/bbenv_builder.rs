use liquid_rust_common::{
    index::{Index, IndexGen, IndexMap},
    ordered_hash_map::OrderedHashMap,
};
use liquid_rust_lrir::{mir::BasicBlock, ty as lr};
use liquid_rust_typeck::BBlockEnv;
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir,
    ty::{self, ParamEnv, TyCtxt},
};
use rustc_mir::dataflow::{
    impls::MaybeUninitializedPlaces,
    move_paths::{LookupResult, MoveData, MovePathIndex},
    Analysis, MoveDataParamEnv,
};

pub struct BBEnvBuilder<'a, 'tcx> {
    body: &'a mir::Body<'tcx>,
    lr_tcx: &'a lr::TyCtxt,
    vars_in_scope: Vec<lr::Var>,
    move_data: &'a MoveData<'tcx>,
    maybe_uninit: &'a BitSet<MovePathIndex>,
    var_gen: IndexGen,
}

impl<'tcx> BBEnvBuilder<'_, 'tcx> {
    pub fn build_envs_for_body(
        body: &mir::Body<'tcx>,
        fn_decl: &lr::FnDecl,
        lr_tcx: &lr::TyCtxt,
        tcx: TyCtxt<'tcx>,
    ) -> IndexMap<BasicBlock, BBlockEnv> {
        let param_env = tcx.param_env(body.source.def_id());
        let move_data = MoveData::gather_moves(body, tcx, param_env).unwrap();
        let mdpe = mk_mpde(
            MoveData::gather_moves(body, tcx, param_env).unwrap(),
            param_env,
        );

        let flow_uninit = MaybeUninitializedPlaces::new(tcx, body, &mdpe)
            .into_engine(tcx, body)
            .iterate_to_fixpoint();

        body.basic_blocks()
            .indices()
            .map(|bb| {
                let vars_in_scope = fn_decl
                    .requires
                    .iter()
                    .map(|(gv, _)| (*gv).into())
                    .collect();
                let builder = BBEnvBuilder {
                    lr_tcx,
                    vars_in_scope,
                    body,
                    move_data: &move_data,
                    maybe_uninit: flow_uninit.entry_set_for_block(bb),
                    var_gen: IndexGen::new(),
                };
                builder.build()
            })
            .collect()
    }

    fn build(mut self) -> BBlockEnv {
        let mut ghost_vars = OrderedHashMap::new();
        let mut locals = vec![];
        for (local, local_decl) in self.body.local_decls.iter_enumerated() {
            let fresh_gv = self.var_gen.fresh();
            let ty = self.lower_ty(local_decl.ty, local, &mut vec![]);
            ghost_vars.insert(fresh_gv, ty);
            self.vars_in_scope.push(lr::Var::from(fresh_gv));
            locals.push((lr::Local::new(local.index()), fresh_gv));
        }
        BBlockEnv { ghost_vars, locals }
    }

    fn lower_ty(
        &mut self,
        ty: ty::Ty<'tcx>,
        local: mir::Local,
        projection: &mut Vec<mir::PlaceElem<'tcx>>,
    ) -> lr::Ty {
        let place = mir::PlaceRef { local, projection };
        if self.is_maybe_uninit(place) {
            return self.lower_uninitialized_ty(ty);
        }

        match ty.kind() {
            ty::TyKind::Tuple(_) => self.lr_tcx.mk_tuple(
                ty.tuple_fields()
                    .enumerate()
                    .map(|(i, ty)| {
                        projection.push(mir::PlaceElem::Field(mir::Field::from_usize(i), ty));
                        let fld = lr::Field::new(i);
                        self.vars_in_scope.push(fld.into());
                        let r = (fld, self.lower_ty(ty, local, projection));
                        self.vars_in_scope.pop();
                        projection.pop();
                        r
                    })
                    .collect(),
            ),
            ty::TyKind::Bool => self.lr_tcx.mk_refine(lr::BaseTy::Bool, self.fresh_kvar()),
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) => {
                self.lr_tcx.mk_refine(lr::BaseTy::Int, self.fresh_kvar())
            }
            ty::TyKind::Ref(..) => todo!(),
            _ => todo!(),
        }
    }

    fn lower_initialized_ty(&mut self, ty: ty::Ty<'tcx>) -> lr::Ty {
        match ty.kind() {
            ty::TyKind::Tuple(_) => self.lr_tcx.mk_tuple(
                ty.tuple_fields()
                    .enumerate()
                    .map(|(i, ty)| {
                        let fld = lr::Field::new(i);
                        self.vars_in_scope.push(fld.into());
                        let r = (fld, self.lower_initialized_ty(ty));
                        self.vars_in_scope.pop();
                        r
                    })
                    .collect(),
            ),
            ty::TyKind::Bool => self.lr_tcx.mk_refine(lr::BaseTy::Bool, self.fresh_kvar()),
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) => {
                self.lr_tcx.mk_refine(lr::BaseTy::Int, self.fresh_kvar())
            }
            ty::TyKind::Ref(..) => todo!(),
            _ => todo!(),
        }
    }

    fn lower_uninitialized_ty(&mut self, ty: ty::Ty<'tcx>) -> lr::Ty {
        match ty.kind() {
            ty::TyKind::Tuple(_) => self.lr_tcx.mk_tuple(
                ty.tuple_fields()
                    .enumerate()
                    .map(|(i, ty)| {
                        let fld = lr::Field::new(i);
                        self.vars_in_scope.push(fld.into());
                        let r = (fld, self.lower_uninitialized_ty(ty));
                        self.vars_in_scope.pop();
                        r
                    })
                    .collect(),
            ),
            // FIXME: Consider real size of type
            ty::TyKind::Bool | ty::TyKind::Ref(..) | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => {
                self.lr_tcx.mk_uninit(1)
            }
            _ => todo!(),
        }
    }

    fn is_maybe_uninit(&self, place: mir::PlaceRef) -> bool {
        let move_path_index = match self.move_data.rev_lookup.find(place) {
            LookupResult::Exact(move_path_index) | LookupResult::Parent(Some(move_path_index)) => {
                move_path_index
            }
            LookupResult::Parent(None) => unreachable!(),
        };
        self.maybe_uninit.contains(move_path_index)
    }

    fn fresh_kvar(&mut self) -> lr::Kvar {
        lr::Kvar {
            id: self.lr_tcx.fresh_kvid(),
            vars: self.vars_in_scope.clone(),
        }
    }
}

fn mk_mpde<'tcx>(move_data: MoveData<'tcx>, param_env: ParamEnv<'tcx>) -> MoveDataParamEnv<'tcx> {
    // FIXME: Ugly hack, but we need a MoveDataParamEnv to call the mir dataflow and
    // fields in MoveDataParamEnv are private.
    struct MPDE<'tcx> {
        move_data: MoveData<'tcx>,
        param_env: ParamEnv<'tcx>,
    }
    let res = MPDE {
        move_data,
        param_env,
    };

    unsafe { std::mem::transmute::<MPDE<'tcx>, MoveDataParamEnv<'tcx>>(res) }
}
