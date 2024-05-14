use std::collections::hash_map::Entry;

use flux_middle::global_env::GlobalEnv;
use rustc_data_structures::{fx::FxIndexSet, sync::Lrc};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_metadata::errors::FailCreateFileEncoder;
use rustc_middle::{
    bug,
    ty::{self, TyCtxt},
};
use rustc_serialize::{opaque, Encodable, Encoder};
use rustc_session::config::CrateType;
use rustc_span::{
    def_id::{CrateNum, DefIndex},
    hygiene::{ExpnIndex, HygieneEncodeContext},
    ExpnId, ExternalSource, SourceFile, Span, SpanData, SpanEncoder, Symbol, SyntaxContext,
};
use rustc_type_ir::TyEncoder;

use crate::{
    CrateMetadata, SpanKind, SpanTag, METADATA_HEADER, SYMBOL_OFFSET, SYMBOL_PREINTERNED,
    SYMBOL_STR,
};

struct EncodeContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: opaque::FileEncoder,
    span_shorthands: FxHashMap<Span, usize>,
    type_shorthands: FxHashMap<ty::Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
    source_file_cache: (Lrc<SourceFile>, usize),
    required_source_files: Option<FxIndexSet<usize>>,
    is_proc_macro: bool,
    hygiene_ctxt: &'a HygieneEncodeContext,
    symbol_table: FxHashMap<Symbol, usize>, // interpret_allocs: FxIndexSet<interpret::AllocId>,
}

pub fn encode_metadata(genv: &GlobalEnv, path: &std::path::Path) {
    let mut encoder = opaque::FileEncoder::new(path).unwrap_or_else(|err| {
        genv.tcx()
            .sess
            .dcx()
            .emit_fatal(FailCreateFileEncoder { err })
    });

    encoder.emit_raw_bytes(METADATA_HEADER);

    let crate_root = CrateMetadata::new(genv);

    let source_map_files = genv.tcx().sess.source_map().files();
    let source_file_cache = (source_map_files[0].clone(), 0);
    let required_source_files = Some(FxIndexSet::default());
    drop(source_map_files);

    let hygiene_ctxt = HygieneEncodeContext::default();
    let mut ecx = EncodeContext {
        tcx: genv.tcx(),
        opaque: encoder,
        span_shorthands: Default::default(),
        type_shorthands: Default::default(),
        predicate_shorthands: Default::default(),
        source_file_cache,
        required_source_files,
        is_proc_macro: genv.tcx().crate_types().contains(&CrateType::ProcMacro),
        hygiene_ctxt: &hygiene_ctxt,
        symbol_table: Default::default(),
    };

    crate_root.encode(&mut ecx);

    ecx.opaque.finish().unwrap();
}

impl<'a, 'tcx> SpanEncoder for EncodeContext<'a, 'tcx> {
    fn encode_crate_num(&mut self, crate_num: CrateNum) {
        if crate_num != LOCAL_CRATE && self.is_proc_macro {
            panic!("Attempted to encode non-local CrateNum {crate_num:?} for proc-macro crate");
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

    fn encode_span(&mut self, span: Span) {
        match self.span_shorthands.entry(span) {
            Entry::Occupied(o) => {
                // If an offset is smaller than the absolute position, we encode with the offset.
                // This saves space since smaller numbers encode in less bits.
                let last_location = *o.get();
                // This cannot underflow. Metadata is written with increasing position(), so any
                // previously saved offset must be smaller than the current position.
                let offset = self.opaque.position() - last_location;
                if offset < last_location {
                    let needed = bytes_needed(offset);
                    SpanTag::indirect(true, needed as u8).encode(self);
                    self.opaque.write_with(|dest| {
                        *dest = offset.to_le_bytes();
                        needed
                    });
                } else {
                    let needed = bytes_needed(last_location);
                    SpanTag::indirect(false, needed as u8).encode(self);
                    self.opaque.write_with(|dest| {
                        *dest = last_location.to_le_bytes();
                        needed
                    });
                }
            }
            Entry::Vacant(v) => {
                let position = self.opaque.position();
                v.insert(position);
                // Data is encoded with a SpanTag prefix (see below).
                span.data().encode(self);
            }
        }
    }

    fn encode_symbol(&mut self, symbol: Symbol) {
        // if symbol preinterned, emit tag and symbol index
        if symbol.is_preinterned() {
            self.opaque.emit_u8(SYMBOL_PREINTERNED);
            self.opaque.emit_u32(symbol.as_u32());
        } else {
            // otherwise write it as string or as offset to it
            match self.symbol_table.entry(symbol) {
                Entry::Vacant(o) => {
                    self.opaque.emit_u8(SYMBOL_STR);
                    let pos = self.opaque.position();
                    o.insert(pos);
                    self.emit_str(symbol.as_str());
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

impl<'a, 'tcx> TyEncoder for EncodeContext<'a, 'tcx> {
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

impl<'a, 'tcx> Encoder for EncodeContext<'a, 'tcx> {
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

fn bytes_needed(n: usize) -> usize {
    (usize::BITS - n.leading_zeros()).div_ceil(u8::BITS) as usize
}

impl<'a, 'tcx> Encodable<EncodeContext<'a, 'tcx>> for SpanData {
    fn encode(&self, s: &mut EncodeContext<'a, 'tcx>) {
        // Don't serialize any `SyntaxContext`s from a proc-macro crate,
        // since we don't load proc-macro dependencies during serialization.
        // This means that any hygiene information from macros used *within*
        // a proc-macro crate (e.g. invoking a macro that expands to a proc-macro
        // definition) will be lost.
        //
        // This can show up in two ways:
        //
        // 1. Any hygiene information associated with identifier of
        // a proc macro (e.g. `#[proc_macro] pub fn $name`) will be lost.
        // Since proc-macros can only be invoked from a different crate,
        // real code should never need to care about this.
        //
        // 2. Using `Span::def_site` or `Span::mixed_site` will not
        // include any hygiene information associated with the definition
        // site. This means that a proc-macro cannot emit a `$crate`
        // identifier which resolves to one of its dependencies,
        // which also should never come up in practice.
        //
        // Additionally, this affects `Span::parent`, and any other
        // span inspection APIs that would otherwise allow traversing
        // the `SyntaxContexts` associated with a span.
        //
        // None of these user-visible effects should result in any
        // cross-crate inconsistencies (getting one behavior in the same
        // crate, and a different behavior in another crate) due to the
        // limited surface that proc-macros can expose.
        //
        // IMPORTANT: If this is ever changed, be sure to update
        // `rustc_span::hygiene::raw_encode_expn_id` to handle
        // encoding `ExpnData` for proc-macro crates.
        let ctxt = if s.is_proc_macro { SyntaxContext::root() } else { self.ctxt };

        if self.is_dummy() {
            let tag = SpanTag::new(SpanKind::Partial, ctxt, 0);
            tag.encode(s);
            if tag.context().is_none() {
                ctxt.encode(s);
            }
            return;
        }

        // The Span infrastructure should make sure that this invariant holds:
        debug_assert!(self.lo <= self.hi);

        if !s.source_file_cache.0.contains(self.lo) {
            let source_map = s.tcx.sess.source_map();
            let source_file_index = source_map.lookup_source_file_idx(self.lo);
            s.source_file_cache =
                (source_map.files()[source_file_index].clone(), source_file_index);
        }
        let (ref source_file, source_file_index) = s.source_file_cache;
        debug_assert!(source_file.contains(self.lo));

        if !source_file.contains(self.hi) {
            // Unfortunately, macro expansion still sometimes generates Spans
            // that malformed in this way.
            let tag = SpanTag::new(SpanKind::Partial, ctxt, 0);
            tag.encode(s);
            if tag.context().is_none() {
                ctxt.encode(s);
            }
            return;
        }

        // There are two possible cases here:
        // 1. This span comes from a 'foreign' crate - e.g. some crate upstream of the
        // crate we are writing metadata for. When the metadata for *this* crate gets
        // deserialized, the deserializer will need to know which crate it originally came
        // from. We use `TAG_VALID_SPAN_FOREIGN` to indicate that a `CrateNum` should
        // be deserialized after the rest of the span data, which tells the deserializer
        // which crate contains the source map information.
        // 2. This span comes from our own crate. No special handling is needed - we just
        // write `TAG_VALID_SPAN_LOCAL` to let the deserializer know that it should use
        // our own source map information.
        //
        // If we're a proc-macro crate, we always treat this as a local `Span`.
        // In `encode_source_map`, we serialize foreign `SourceFile`s into our metadata
        // if we're a proc-macro crate.
        // This allows us to avoid loading the dependencies of proc-macro crates: all of
        // the information we need to decode `Span`s is stored in the proc-macro crate.
        let (kind, metadata_index) = if source_file.is_imported() && !s.is_proc_macro {
            // To simplify deserialization, we 'rebase' this span onto the crate it originally came
            // from (the crate that 'owns' the file it references. These rebased 'lo' and 'hi'
            // values are relative to the source map information for the 'foreign' crate whose
            // CrateNum we write into the metadata. This allows `imported_source_files` to binary
            // search through the 'foreign' crate's source map information, using the
            // deserialized 'lo' and 'hi' values directly.
            //
            // All of this logic ensures that the final result of deserialization is a 'normal'
            // Span that can be used without any additional trouble.
            let metadata_index = {
                // Introduce a new scope so that we drop the 'read()' temporary
                match &*source_file.external_src.read() {
                    ExternalSource::Foreign { metadata_index, .. } => *metadata_index,
                    src => panic!("Unexpected external source {src:?}"),
                }
            };

            (SpanKind::Foreign, metadata_index)
        } else {
            // Record the fact that we need to encode the data for this `SourceFile`
            let source_files = s
                .required_source_files
                .as_mut()
                .expect("Already encoded SourceMap!");
            let (metadata_index, _) = source_files.insert_full(source_file_index);
            let metadata_index: u32 = metadata_index
                .try_into()
                .expect("cannot export more than U32_MAX files");

            (SpanKind::Local, metadata_index)
        };

        // Encode the start position relative to the file start, so we profit more from the
        // variable-length integer encoding.
        let lo = self.lo - source_file.start_pos;

        // Encode length which is usually less than span.hi and profits more
        // from the variable-length integer encoding that we use.
        let len = self.hi - self.lo;

        let tag = SpanTag::new(kind, ctxt, len.0 as usize);
        tag.encode(s);
        if tag.context().is_none() {
            ctxt.encode(s);
        }
        lo.encode(s);
        if tag.length().is_none() {
            len.encode(s);
        }

        // Encode the index of the `SourceFile` for the span, in order to make decoding faster.
        metadata_index.encode(s);

        if kind == SpanKind::Foreign {
            // This needs to be two lines to avoid holding the `s.source_file_cache`
            // while calling `cnum.encode(s)`
            let cnum = s.source_file_cache.0.cnum;
            cnum.encode(s);
        }
    }
}
