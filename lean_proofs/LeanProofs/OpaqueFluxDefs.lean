-- OPAQUE DEFS --
class FluxDefs where
  VSeq (t0 : Type) [Inhabited t0] : Type
  svec_vseq_empty : {t0 : Type} -> [Inhabited t0] -> (VSeq t0)
  svec_vseq_singleton : {t0 : Type} -> [Inhabited t0] -> (t0 -> (VSeq t0))
  svec_vseq_append : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> ((VSeq t0) -> (VSeq t0)))
  svec_vseq_get : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> t0))
  svec_vseq_set : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> (t0 -> (VSeq t0))))
  svec_vseq_slice : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> (Int -> (Int -> (VSeq t0))))
  svec_vseq_len : {t0 : Type} -> [Inhabited t0] -> ((VSeq t0) -> Int)
