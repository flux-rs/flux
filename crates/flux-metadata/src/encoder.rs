use std::{collections::hash_map::Entry, sync::Arc};

use flux_middle::global_env::GlobalEnv;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_metadata::errors::FailCreateFileEncoder;
use rustc_middle::{
    bug,
    ty::{self, TyCtxt, codec::TyEncoder},
};
use rustc_serialize::{Encodable, Encoder, opaque, opaque::IntEncodedWithFixedSize};
use rustc_session::config::CrateType;
use rustc_span::{
    ByteSymbol, ExpnId, SourceFile, Span, SpanEncoder, Symbol, SyntaxContext,
    def_id::{CrateNum, DefIndex},
    hygiene::{ExpnIndex, HygieneEncodeContext},
};

use crate::{
    AbsoluteBytePos, CrateMetadata, EncodedSourceFileId, Footer, METADATA_HEADER, SYMBOL_OFFSET,
    SYMBOL_PREDEFINED, SYMBOL_STR, SourceFileIndex, TAG_FULL_SPAN, TAG_PARTIAL_SPAN,
    rustc_middle::dep_graph::DepContext,
};

struct EncodeContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: opaque::FileEncoder,
    type_shorthands: FxHashMap<ty::Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
    file_to_file_index: FxHashMap<*const SourceFile, SourceFileIndex>,
    is_proc_macro: bool,
    hygiene_ctxt: &'a HygieneEncodeContext,
    symbol_index_table: FxHashMap<u32, usize>,
}

impl EncodeContext<'_, '_> {
    fn source_file_index(&mut self, source_file: Arc<SourceFile>) -> SourceFileIndex {
        self.file_to_file_index[&(&*source_file as *const SourceFile)]
    }

    fn encode_symbol_or_byte_symbol(
        &mut self,
        index: u32,
        emit_str_or_byte_str: impl Fn(&mut Self),
    ) {
        // if symbol/byte symbol is predefined, emit tag and symbol index
        // TODO: we could also encode flux predefined symbols like this
        if Symbol::is_predefined(index) {
            self.opaque.emit_u8(SYMBOL_PREDEFINED);
            self.opaque.emit_u32(index);
        } else {
            // otherwise write it as string or as offset to it
            match self.symbol_index_table.entry(index) {
                Entry::Vacant(o) => {
                    self.opaque.emit_u8(SYMBOL_STR);
                    let pos = self.opaque.position();
                    o.insert(pos);
                    emit_str_or_byte_str(self);
                }
                Entry::Occupied(o) => {
                    let x = *o.get();
                    self.emit_u8(SYMBOL_OFFSET);
                    self.emit_usize(x);
                }
            }
        }
    }
}

fn file_indices(
    tcx: TyCtxt,
) -> (FxHashMap<*const SourceFile, SourceFileIndex>, FxHashMap<SourceFileIndex, EncodedSourceFileId>)
{
    let files = tcx.sess.source_map().files();
    let mut file_to_file_index =
        FxHashMap::with_capacity_and_hasher(files.len(), Default::default());
    let mut file_index_to_stable_id =
        FxHashMap::with_capacity_and_hasher(files.len(), Default::default());
    use rustc_span::def_id::LOCAL_CRATE;
    let source_map = tcx.sess.source_map();
    let working_directory = &tcx.sess.opts.working_dir;
    let local_crate_stable_id = tcx.stable_crate_id(LOCAL_CRATE);

    // This portion of the code is adapted from the rustc metadata encoder, while the rest of
    // the code in this file is based off the rustc incremental cache encoder.
    //
    // Probably we should refactor the code to be exclusively based on the metadata encoder
    for (index, file) in files.iter().enumerate() {
        let index = SourceFileIndex(index as u32);
        let file_ptr: *const SourceFile = &**file as *const _;
        file_to_file_index.insert(file_ptr, index);

        let mut adapted_source_file = (**file).clone();
        if adapted_source_file.cnum == LOCAL_CRATE {
            use rustc_span::FileName;
            match file.name {
                FileName::Real(ref original_file_name) => {
                    let adapted_file_name = source_map
                        .path_mapping()
                        .to_embeddable_absolute_path(original_file_name.clone(), working_directory);

                    adapted_source_file.name = FileName::Real(adapted_file_name);
                }
                _ => {
                    // expanded code, not from a file
                }
            };
            use rustc_span::StableSourceFileId;
            adapted_source_file.stable_id = StableSourceFileId::from_filename_for_export(
                &adapted_source_file.name,
                local_crate_stable_id,
            );
        }

        let source_file_id = EncodedSourceFileId::new(tcx, &adapted_source_file);
        file_index_to_stable_id.insert(index, source_file_id);
    }

    (file_to_file_index, file_index_to_stable_id)
}

pub fn encode_metadata(genv: GlobalEnv, path: &std::path::Path) {
    let (file_to_file_index, file_index_to_stable_id) = file_indices(genv.tcx());

    let mut encoder = opaque::FileEncoder::new(path).unwrap_or_else(|err| {
        genv.tcx()
            .sess
            .dcx()
            .emit_fatal(FailCreateFileEncoder { err })
    });

    encoder.emit_raw_bytes(METADATA_HEADER);

    let crate_root = CrateMetadata::new(genv);

    let hygiene_ctxt = HygieneEncodeContext::default();
    let tcx = genv.tcx();
    let mut ecx = EncodeContext {
        tcx,
        opaque: encoder,
        type_shorthands: Default::default(),
        predicate_shorthands: Default::default(),
        file_to_file_index,
        is_proc_macro: genv.tcx().crate_types().contains(&CrateType::ProcMacro),
        hygiene_ctxt: &hygiene_ctxt,
        symbol_index_table: Default::default(),
    };

    crate_root.encode(&mut ecx);

    // BEGIN: CREUSOT-footer
    let mut syntax_contexts = FxHashMap::default();
    let mut expn_data = FxHashMap::default();

    // Encode all hygiene data (`SyntaxContextData` and `ExpnData`) from the current session.
    ecx.hygiene_ctxt.encode(
        &mut ecx,
        |encoder, index, ctxt_data| {
            let pos = AbsoluteBytePos::new(encoder.position());
            ctxt_data.encode(encoder);
            syntax_contexts.insert(index, pos);
        },
        |encoder, expn_id, data, hash| {
            let pos = AbsoluteBytePos::new(encoder.position());
            data.encode(encoder);
            hash.encode(encoder);
            expn_data.insert((tcx.stable_crate_id(expn_id.krate), expn_id.local_id.as_u32()), pos);
        },
    );

    // Encode the file footer.
    let footer_pos = ecx.position() as u64;
    let footer = Footer { file_index_to_stable_id, syntax_contexts, expn_data };
    footer.encode(&mut ecx);

    // Encode the position of the footer as the last 8 bytes of the
    // file so we know where to look for it.
    IntEncodedWithFixedSize(footer_pos).encode(&mut ecx.opaque);

    // DO NOT WRITE ANYTHING TO THE ENCODER AFTER THIS POINT! The address
    // of the footer must be the last thing in the data stream.
    // END: CREUSOT-footer

    ecx.opaque.finish().unwrap();
}

impl SpanEncoder for EncodeContext<'_, '_> {
    fn encode_crate_num(&mut self, crate_num: CrateNum) {
        if crate_num != LOCAL_CRATE && self.is_proc_macro {
            bug!("Attempted to encode non-local CrateNum {crate_num:?} for proc-macro crate");
        }
        self.tcx.stable_crate_id(crate_num).encode(self);
    }

    fn encode_def_index(&mut self, def_index: DefIndex) {
        self.emit_u32(def_index.as_u32());
    }

    fn encode_def_id(&mut self, def_id: DefId) {
        def_id.krate.encode(self);
        def_id.index.encode(self);
    }

    fn encode_syntax_context(&mut self, syntax_context: SyntaxContext) {
        rustc_span::hygiene::raw_encode_syntax_context(syntax_context, self.hygiene_ctxt, self);
    }

    fn encode_expn_id(&mut self, expn_id: ExpnId) {
        if expn_id.krate == LOCAL_CRATE {
            // We will only write details for local expansions. Non-local expansions will fetch
            // data from the corresponding crate's metadata.
            // FIXME(#43047) FIXME(#74731) We may eventually want to avoid relying on external
            // metadata from proc-macro crates.
            self.hygiene_ctxt.schedule_expn_data_for_encoding(expn_id);
        }
        expn_id.krate.encode(self);
        expn_id.local_id.encode(self);
    }

    // Code adapted from creusot
    fn encode_span(&mut self, span: Span) {
        let span = span.data();
        span.ctxt.encode(self);

        if span.is_dummy() {
            return TAG_PARTIAL_SPAN.encode(self);
        }

        let source_file = self.tcx.sess().source_map().lookup_source_file(span.lo);
        if !source_file.contains(span.hi) {
            // Unfortunately, macro expansion still sometimes generates Spans
            // that malformed in this way.
            return TAG_PARTIAL_SPAN.encode(self);
        }

        let lo = span.lo - source_file.start_pos;
        let len = span.hi - span.lo;
        let source_file_index = self.source_file_index(source_file);

        TAG_FULL_SPAN.encode(self);
        source_file_index.encode(self);
        lo.encode(self);
        len.encode(self);
    }

    fn encode_symbol(&mut self, sym: Symbol) {
        self.encode_symbol_or_byte_symbol(sym.as_u32(), |this| this.emit_str(sym.as_str()));
    }

    fn encode_byte_symbol(&mut self, byte_sym: ByteSymbol) {
        self.encode_symbol_or_byte_symbol(byte_sym.as_u32(), |this| {
            this.emit_byte_str(byte_sym.as_byte_str());
        });
    }
}

impl<'tcx> TyEncoder<'tcx> for EncodeContext<'_, 'tcx> {
    const CLEAR_CROSS_CRATE: bool = true;

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

impl<'a, 'tcx> Encodable<EncodeContext<'a, 'tcx>> for ExpnIndex {
    fn encode(&self, s: &mut EncodeContext<'a, 'tcx>) {
        s.emit_u32(self.as_u32());
    }
}

macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) {
            self.opaque.$name(value)
        })*
    }
}

impl Encoder for EncodeContext<'_, '_> {
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
