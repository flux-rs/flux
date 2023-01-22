use std::{fs, io::Read, mem, path::Path};

use flux_common::bug;
use flux_errors::FluxSession;
use rustc_data_structures::sync::HashMapExt;
use rustc_middle::{
    implement_ty_decoder,
    ty::{self, TyCtxt},
};
use rustc_serialize::{opaque::MemDecoder, Decodable, Decoder};
use rustc_span::def_id::{CrateNum, DefIndex, StableCrateId};
use rustc_type_ir::TyDecoder;

use crate::{CrateMetadata, METADATA_HEADER};

struct DecodeContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: MemDecoder<'a>,
}

pub(super) fn decode_crate_metadata(
    tcx: TyCtxt,
    _sess: &FluxSession,
    path: &Path,
) -> CrateMetadata {
    let mut file = fs::File::open(path).unwrap();
    let mut buf = vec![];
    file.read_to_end(&mut buf).unwrap();

    if !buf.starts_with(METADATA_HEADER) {
        todo!()
    }

    let mut decoder = DecodeContext { tcx, opaque: MemDecoder::new(&buf, METADATA_HEADER.len()) };
    CrateMetadata::decode(&mut decoder)
}

impl<'a, 'tcx> Decodable<DecodeContext<'a, 'tcx>> for CrateNum {
    fn decode(d: &mut DecodeContext<'a, 'tcx>) -> Self {
        let stable_id = StableCrateId::decode(d);
        d.tcx.stable_crate_id_to_crate_num(stable_id)
    }
}

impl<'a, 'tcx> Decodable<DecodeContext<'a, 'tcx>> for DefIndex {
    fn decode(d: &mut DecodeContext<'a, 'tcx>) -> Self {
        DefIndex::from_u32(d.read_u32())
    }
}

implement_ty_decoder!(DecodeContext<'a, 'tcx>);

impl<'a, 'tcx> TyDecoder for DecodeContext<'a, 'tcx> {
    type I = TyCtxt<'tcx>;

    const CLEAR_CROSS_CRATE: bool = true;

    fn interner(&self) -> Self::I {
        self.tcx
    }

    fn peek_byte(&self) -> u8 {
        self.opaque.data[self.opaque.position()]
    }

    fn position(&self) -> usize {
        self.opaque.position()
    }

    fn cached_ty_for_shorthand<F>(&mut self, shorthand: usize, or_insert_with: F) -> ty::Ty<'tcx>
    where
        F: FnOnce(&mut Self) -> ty::Ty<'tcx>,
    {
        let tcx = self.tcx;

        let cache_key = ty::CReaderCacheKey { cnum: None, pos: shorthand };

        if let Some(&ty) = tcx.ty_rcache.borrow().get(&cache_key) {
            return ty;
        }

        let ty = or_insert_with(self);
        // This may overwrite the entry, but it should overwrite with the same value.
        tcx.ty_rcache.borrow_mut().insert_same(cache_key, ty);
        ty
    }

    fn with_position<F, R>(&mut self, pos: usize, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        debug_assert!(pos < self.opaque.data.len());

        let new_opaque = MemDecoder::new(self.opaque.data, pos);
        let old_opaque = mem::replace(&mut self.opaque, new_opaque);
        let r = f(self);
        self.opaque = old_opaque;
        r
    }

    fn decode_alloc_id(&mut self) -> rustc_middle::mir::interpret::AllocId {
        bug!("Encoding `interpret::AllocId` is not supported")
    }
}
