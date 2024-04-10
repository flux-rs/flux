use flux_middle::global_env::GlobalEnv;
use rustc_hash::FxHashMap;
use rustc_metadata::errors::FailCreateFileEncoder;
use rustc_middle::{
    bug,
    ty::{self, TyCtxt},
};
use rustc_serialize::{opaque, Encodable, Encoder};
use rustc_span::{
    def_id::{CrateNum, DefIndex},
    SpanEncoder,
};
use rustc_type_ir::TyEncoder;

use crate::{CrateMetadata, METADATA_HEADER};

struct EncodeContext<'tcx> {
    _tcx: TyCtxt<'tcx>,
    opaque: opaque::FileEncoder,
    type_shorthands: FxHashMap<ty::Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,
    // interpret_allocs: FxIndexSet<interpret::AllocId>,
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

    let mut ecx = EncodeContext {
        _tcx: genv.tcx(),
        opaque: encoder,
        type_shorthands: Default::default(),
        predicate_shorthands: Default::default(),
    };

    crate_root.encode(&mut ecx);

    ecx.opaque.finish().unwrap();
}

impl<'tcx> SpanEncoder for EncodeContext<'tcx> {
    fn encode_span(&mut self, span: rustc_span::Span) {
        self.opaque.encode_span(span);
    }

    fn encode_symbol(&mut self, symbol: rustc_span::Symbol) {
        self.opaque.encode_symbol(symbol);
    }

    fn encode_expn_id(&mut self, expn_id: rustc_span::ExpnId) {
        self.opaque.encode_expn_id(expn_id);
    }

    fn encode_syntax_context(&mut self, syntax_context: rustc_span::SyntaxContext) {
        self.opaque.encode_syntax_context(syntax_context);
    }

    fn encode_crate_num(&mut self, crate_num: CrateNum) {
        self.opaque.encode_crate_num(crate_num);
    }

    fn encode_def_index(&mut self, def_index: DefIndex) {
        self.opaque.encode_def_index(def_index);
    }

    fn encode_def_id(&mut self, def_id: rustc_hir::def_id::DefId) {
        self.opaque.encode_def_id(def_id);
    }
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
