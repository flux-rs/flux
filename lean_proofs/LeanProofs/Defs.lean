import LeanProofs.InferredInstance
-- FUNC DECLS --
mutual
def svec_iseq_push (a0 : (VSeq Int)) (a1 : Int) : (VSeq Int) :=
  (svec_vseq_append a0 (svec_vseq_singleton a1))

def svec_iseq_pop (a2 : (VSeq Int)) : Int :=
  (svec_vseq_get a2 ((svec_vseq_len a2) - 1))

end
