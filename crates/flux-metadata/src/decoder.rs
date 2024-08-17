use std::{
    fs,
    io::{self, Read},
    mem,
    path::Path,
};

use flux_common::bug;
use flux_errors::FluxSession;
use rustc_data_structures::sync::HashMapExt;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    implement_ty_decoder,
    ty::{self, TyCtxt},
};
use rustc_serialize::{opaque::MemDecoder, Decodable, Decoder as _};
use rustc_session::StableCrateId;
use rustc_span::{
    def_id::{CrateNum, DefIndex},
    BytePos, Span, SpanDecoder, StableSourceFileId, Symbol, SyntaxContext,
};
use rustc_type_ir::TyDecoder;

use crate::{CrateMetadata, METADATA_HEADER, SYMBOL_OFFSET, SYMBOL_PREINTERNED, SYMBOL_STR};

struct DecodeContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: MemDecoder<'a>,
}

pub(super) fn decode_crate_metadata(
    tcx: TyCtxt,
    sess: &FluxSession,
    path: &Path,
) -> Option<CrateMetadata> {
    let mut file = match fs::File::open(path) {
        Ok(file) => file,
        Err(err) if let io::ErrorKind::NotFound = err.kind() => return None,
        Err(err) => sess.emit_fatal(errors::DecodeFileError::new(path, err)),
    };
    let mut buf = vec![];
    file.read_to_end(&mut buf)
        .unwrap_or_else(|err| sess.emit_fatal(errors::DecodeFileError::new(path, err)));

    if !buf.starts_with(METADATA_HEADER) {
        bug!("incompatible metadata version");
    }

    let mut decoder =
        DecodeContext { tcx, opaque: MemDecoder::new(&buf, METADATA_HEADER.len()).unwrap() };
    Some(CrateMetadata::decode(&mut decoder))
}

implement_ty_decoder!(DecodeContext<'a, 'tcx>);

impl<'a, 'tcx> SpanDecoder for DecodeContext<'a, 'tcx> {
    fn decode_attr_id(&mut self) -> rustc_ast::AttrId {
        self.tcx.sess.psess.attr_id_generator.mk_attr_id()
    }

    fn decode_crate_num(&mut self) -> CrateNum {
        let stable_id = StableCrateId::decode(self);
        self.tcx.stable_crate_id_to_crate_num(stable_id)
    }

    fn decode_def_index(&mut self) -> DefIndex {
        DefIndex::from_u32(self.read_u32())
    }

    fn decode_def_id(&mut self) -> DefId {
        DefId { krate: Decodable::decode(self), index: Decodable::decode(self) }
    }

    fn decode_syntax_context(&mut self) -> rustc_span::SyntaxContext {
        bug!("cannot decode `SyntaxContext` with `DecodeContext`");
    }

    fn decode_expn_id(&mut self) -> rustc_span::ExpnId {
        bug!("cannot decode `ExpnId` with `DecodeContext`");
    }

    fn decode_span(&mut self) -> rustc_span::Span {
        let sm = self.tcx.sess.source_map();
        let pos = [(); 2].map(|_| {
            let ssfi = StableSourceFileId::decode(self);
            let rel_bp = BytePos::decode(self);
            // See comment in 'encoder.rs'
            //
            // This should hopefully never fail,
            // so maybe could be an `unwrap` instead?
            sm.source_file_by_stable_id(ssfi)
                .map_or(BytePos(0), |sf| sf.start_pos + rel_bp)
        });
        Span::new(pos[0], pos[1], SyntaxContext::root(), None)
    }

    fn decode_symbol(&mut self) -> rustc_span::Symbol {
        let tag = self.read_u8();

        match tag {
            SYMBOL_STR => {
                let s = self.read_str();
                Symbol::intern(s)
            }
            SYMBOL_OFFSET => {
                // read str offset
                let pos = self.read_usize();

                // move to str offset and read
                self.opaque.with_position(pos, |d| {
                    let s = d.read_str();
                    Symbol::intern(s)
                })
            }
            SYMBOL_PREINTERNED => {
                let symbol_index = self.read_u32();
                Symbol::new_from_decoded(symbol_index)
            }
            _ => unreachable!(),
        }
    }
}

impl<'a, 'tcx> TyDecoder for DecodeContext<'a, 'tcx> {
    type I = TyCtxt<'tcx>;

    const CLEAR_CROSS_CRATE: bool = true;

    fn interner(&self) -> Self::I {
        self.tcx
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
        let new_opaque = self.opaque.split_at(pos);
        let old_opaque = mem::replace(&mut self.opaque, new_opaque);
        let r = f(self);
        self.opaque = old_opaque;
        r
    }

    fn decode_alloc_id(&mut self) -> rustc_middle::mir::interpret::AllocId {
        bug!("Encoding `interpret::AllocId` is not supported")
    }
}

mod errors {
    use std::{io, path::Path};

    use flux_errors::E0999;
    use flux_macros::Diagnostic;

    #[derive(Diagnostic)]
    #[diag(metadata_decode_file_error, code = E0999)]
    pub(super) struct DecodeFileError<'a> {
        path: &'a Path,
        err: io::Error,
    }

    impl<'a> DecodeFileError<'a> {
        pub(super) fn new(path: &'a Path, err: io::Error) -> Self {
            Self { path, err }
        }
    }
}
