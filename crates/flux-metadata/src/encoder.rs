use flux_middle::global_env::GlobalEnv;
use rustc_hash::FxHashMap;
use rustc_metadata::errors::FailCreateFileEncoder;
use rustc_middle::{
    bug,
    ty::{self, TyCtxt},
};
use rustc_serialize::{opaque, Encodable, Encoder};
use rustc_span::def_id::{CrateNum, DefIndex};
use rustc_type_ir::TyEncoder;

use crate::{CrateMetadata, METADATA_HEADER};

struct EncodeContext<'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: opaque::FileEncoder,
    type_shorthands: FxHashMap<ty::Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
    // interpret_allocs: FxIndexSet<interpret::AllocId>,
}

pub fn encode_metadata(genv: &GlobalEnv, path: &std::path::Path) {
    let mut encoder = opaque::FileEncoder::new(path)
        .unwrap_or_else(|err| genv.tcx().sess.emit_fatal(FailCreateFileEncoder { err }));

    encoder.emit_raw_bytes(METADATA_HEADER);

    let crate_root = CrateMetadata::new(genv);

    let mut ecx = EncodeContext {
        tcx: genv.tcx(),
        opaque: encoder,
        type_shorthands: Default::default(),
        predicate_shorthands: Default::default(),
    };

    crate_root.encode(&mut ecx);

    ecx.opaque.finish().unwrap();
}

impl<'tcx> TyEncoder for EncodeContext<'tcx> {
    const CLEAR_CROSS_CRATE: bool = true;

    type I = TyCtxt<'tcx>;

    fn position(&self) -> usize {
        self.opaque.position()
    }

    fn type_shorthands(&mut self) -> &mut FxHashMap<ty::Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }

    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, _alloc_id: &rustc_middle::mir::interpret::AllocId) {
        bug!("Encoding `interpret::AllocId` is not supported");
        // let (index, _) = self.interpret_allocs.insert_full(*alloc_id);
        // index.encode(self);
    }
}

impl<'tcx> Encodable<EncodeContext<'tcx>> for DefIndex {
    fn encode(&self, s: &mut EncodeContext<'tcx>) {
        s.emit_u32(self.as_u32());
    }
}

impl<'tcx> Encodable<EncodeContext<'tcx>> for CrateNum {
    fn encode(&self, s: &mut EncodeContext<'tcx>) {
        s.tcx.stable_crate_id(*self).encode(s);
    }
}

macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) {
            self.opaque.$name(value)
        })*
    }
}

impl<'tcx> Encoder for EncodeContext<'tcx> {
    encoder_methods! {
        emit_usize(usize);
        emit_u128(u128);
        emit_u64(u64);
        emit_u32(u32);
        emit_u16(u16);
        emit_u8(u8);

        emit_isize(isize);
        emit_i128(i128);
        emit_i64(i64);
        emit_i32(i32);
        emit_i16(i16);
        emit_i8(i8);

        emit_bool(bool);
        emit_char(char);
        emit_str(&str);
        emit_raw_bytes(&[u8]);
    }
}
