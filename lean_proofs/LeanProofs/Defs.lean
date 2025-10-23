import LeanProofs.InferredInstance
-- FUNC DECLS --
mutual
def svec_iseq_push (a0 : ISeq) (a1 : Int) : ISeq :=
  (svec_iseq_append a0 (svec_iseq_singleton a1))

def svec_iseq_pop (a2 : ISeq) : Int :=
  (svec_iseq_get a2 ((svec_iseq_len a2) - 1))

end
