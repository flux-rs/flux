use std::{
    fs,
    io::{self, Read},
    mem,
    path::Path,
    sync::Arc,
};

use flux_common::bug;
use flux_errors::FluxSession;
use rustc_data_structures::{fx::FxHashMap, sync::HashMapExt};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    implement_ty_decoder,
    ty::{self, TyCtxt, codec::TyDecoder},
};
use rustc_serialize::{
    Decodable, Decoder as _,
    opaque::{IntEncodedWithFixedSize, MemDecoder},
};
use rustc_session::StableCrateId;
use rustc_span::{
    BlobDecoder, BytePos, ByteSymbol, DUMMY_SP, SourceFile, Span, SpanDecoder, Symbol,
    SyntaxContext,
    def_id::{CrateNum, DefIndex},
    hygiene::{HygieneDecodeContext, SyntaxContextKey},
};

use crate::{
    AbsoluteBytePos, CrateMetadata, EncodedSourceFileId, Footer, METADATA_HEADER, SYMBOL_OFFSET,
    SYMBOL_PREDEFINED, SYMBOL_STR, SourceFileIndex, TAG_FULL_SPAN, TAG_PARTIAL_SPAN,
};

struct DecodeContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: MemDecoder<'a>,
    file_index_to_file: FxHashMap<SourceFileIndex, Arc<SourceFile>>,
    file_index_to_stable_id: FxHashMap<SourceFileIndex, EncodedSourceFileId>,
    syntax_contexts: &'a FxHashMap<u32, AbsoluteBytePos>,
    expn_data: FxHashMap<(StableCrateId, u32), AbsoluteBytePos>,
    hygiene_context: &'a HygieneDecodeContext,
}

impl<'a, 'tcx> DecodeContext<'a, 'tcx> {
    fn file_index_to_file(&mut self, index: SourceFileIndex) -> Arc<SourceFile> {
        self.file_index_to_file
            .entry(index)
            .or_insert_with(|| {
                let source_file_id = &self.file_index_to_stable_id[&index];
                let source_file_cnum = self
                    .tcx
                    .stable_crate_id_to_crate_num(source_file_id.stable_crate_id);

                self.tcx.import_source_files(source_file_cnum);
                self.tcx
                    .sess
                    .source_map()
                    .source_file_by_stable_id(source_file_id.stable_source_file_id)
                    .expect("failed to lookup `SourceFile` in new context")
            })
            .clone()
    }
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

    let footer = {
        let mut decoder = MemDecoder::new(&buf, 0).unwrap();
        let footer_pos = decoder
            .with_position(decoder.len() - IntEncodedWithFixedSize::ENCODED_SIZE, |d| {
                IntEncodedWithFixedSize::decode(d).0 as usize
            });
        decoder.with_position(footer_pos, Footer::decode)
    };

    let mut decoder = DecodeContext {
        tcx,
        opaque: MemDecoder::new(&buf, METADATA_HEADER.len()).unwrap(),
        file_index_to_stable_id: footer.file_index_to_stable_id,
        file_index_to_file: Default::default(),
        syntax_contexts: &footer.syntax_contexts,
        expn_data: footer.expn_data,
        hygiene_context: &Default::default(),
    };

    Some(CrateMetadata::decode(&mut decoder))
}

implement_ty_decoder!(DecodeContext<'a, 'tcx>);

impl BlobDecoder for DecodeContext<'_, '_> {
    fn decode_symbol(&mut self) -> Symbol {
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
            SYMBOL_PREDEFINED => {
                let symbol_index = self.read_u32();
                Symbol::new(symbol_index)
            }
            _ => unreachable!(),
        }
    }

    fn decode_byte_symbol(&mut self) -> ByteSymbol {
        ByteSymbol::intern(self.read_byte_str())
    }

    fn decode_def_index(&mut self) -> DefIndex {
        DefIndex::from_u32(self.read_u32())
    }
}

impl SpanDecoder for DecodeContext<'_, '_> {
    fn decode_attr_id(&mut self) -> rustc_ast::AttrId {
        self.tcx.sess.psess.attr_id_generator.mk_attr_id()
    }

    fn decode_crate_num(&mut self) -> CrateNum {
        let stable_id = StableCrateId::decode(self);
        self.tcx.stable_crate_id_to_crate_num(stable_id)
    }

    fn decode_def_id(&mut self) -> DefId {
        DefId { krate: Decodable::decode(self), index: Decodable::decode(self) }
    }

    fn decode_syntax_context(&mut self) -> SyntaxContext {
        let syntax_contexts = self.syntax_contexts;
        rustc_span::hygiene::decode_syntax_context(self, self.hygiene_context, |this, id| {
            // This closure is invoked if we haven't already decoded the data for the `SyntaxContext` we are deserializing.
            // We look up the position of the associated `SyntaxData` and decode it.
            let pos = syntax_contexts.get(&id).unwrap();
            this.with_position(pos.to_usize(), SyntaxContextKey::decode)
        })
    }

    fn decode_expn_id(&mut self) -> rustc_span::ExpnId {
        let stable_id = StableCrateId::decode(self);
        let cnum = self.tcx.stable_crate_id_to_crate_num(stable_id);
        let index = u32::decode(self);

        rustc_span::hygiene::decode_expn_id(cnum, index, |_| {
            let pos = self.expn_data.get(&(stable_id, index)).unwrap();
            self.with_position(pos.to_usize(), |decoder| {
                let data = rustc_span::ExpnData::decode(decoder);
                let hash = rustc_span::ExpnHash::decode(decoder);
                (data, hash)
            })
        })
    }

    fn decode_span(&mut self) -> rustc_span::Span {
        let ctxt = SyntaxContext::decode(self);
        let tag: u8 = Decodable::decode(self);

        if tag == TAG_PARTIAL_SPAN {
            return DUMMY_SP.with_ctxt(ctxt);
        }

        debug_assert!(tag == TAG_FULL_SPAN);

        let source_file_index = SourceFileIndex::decode(self);
        let lo = BytePos::decode(self);
        let len = BytePos::decode(self);
        let file = self.file_index_to_file(source_file_index);
        let lo = file.start_pos + lo;
        let hi = lo + len;

        Span::new(lo, hi, ctxt, None)
    }
}

impl<'tcx> TyDecoder<'tcx> for DecodeContext<'_, 'tcx> {
    const CLEAR_CROSS_CRATE: bool = true;

    fn interner(&self) -> TyCtxt<'tcx> {
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
