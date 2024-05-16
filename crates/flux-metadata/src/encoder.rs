use std::collections::hash_map::Entry;

use flux_middle::global_env::GlobalEnv;
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
    ExpnId, FileName, SourceFile, Span, SpanEncoder, StableSourceFileId, Symbol, SyntaxContext,
};
use rustc_type_ir::TyEncoder;

use crate::{CrateMetadata, METADATA_HEADER, SYMBOL_OFFSET, SYMBOL_PREINTERNED, SYMBOL_STR};

struct EncodeContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: opaque::FileEncoder,
    type_shorthands: FxHashMap<ty::Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
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

    let hygiene_ctxt = HygieneEncodeContext::default();
    let mut ecx = EncodeContext {
        tcx: genv.tcx(),
        opaque: encoder,
        type_shorthands: Default::default(),
        predicate_shorthands: Default::default(),
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

    // Code adapted from prusti
    fn encode_span(&mut self, span: Span) {
        let sm = self.tcx.sess.source_map();
        for bp in [span.lo(), span.hi()] {
            let sf = sm.lookup_source_file(bp);
            let ssfi = stable_source_file_id_for_export(self.tcx, &sf);
            ssfi.encode(self);
            // Not sure if this is the most stable way to encode a BytePos. If it fails
            // try finding a function in `SourceMap` or `SourceFile` instead. E.g. the
            // `bytepos_to_file_charpos` fn which returns `CharPos` (though there is
            // currently no fn mapping back to `BytePos` for decode)
            (bp - sf.start_pos).encode(self);
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

fn stable_source_file_id_for_export(tcx: TyCtxt, sf: &SourceFile) -> StableSourceFileId {
    let working_directory = &tcx.sess.opts.working_dir;
    let crate_stable_id = tcx.stable_crate_id(sf.cnum);
    let mut filename = sf.name.clone();
    if let FileName::Real(original_file_name) = filename {
        let adapted_file_name = tcx
            .sess
            .source_map()
            .path_mapping()
            .to_embeddable_absolute_path(original_file_name.clone(), working_directory);

        filename = FileName::Real(adapted_file_name);
    }
    StableSourceFileId::from_filename_for_export(&filename, crate_stable_id)
}
