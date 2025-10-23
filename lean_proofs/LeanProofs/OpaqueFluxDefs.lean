-- OPAQUE DEFS --
class FluxDefs where
  ISeq  : Type
  svec_iseq_empty : ISeq
  svec_iseq_singleton : (Int -> ISeq)
  svec_iseq_append : (ISeq -> (ISeq -> ISeq))
  svec_iseq_get : (ISeq -> (Int -> Int))
  svec_iseq_set : (ISeq -> (Int -> (Int -> ISeq)))
  svec_iseq_slice : (ISeq -> (Int -> (Int -> ISeq)))
  svec_iseq_len : (ISeq -> Int)
