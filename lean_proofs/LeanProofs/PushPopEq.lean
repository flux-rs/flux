import LeanProofs.Defs
import LeanProofs.InferredInstance
def push_pop_eq := (∀ (reftgen_elems_0 : (VSeq Int)), (∀ (reftgen_v_1 : Int), ((svec_vseq_get (svec_vseq_append reftgen_elems_0 (svec_vseq_singleton reftgen_v_1)) ((svec_vseq_len (svec_vseq_append reftgen_elems_0 (svec_vseq_singleton reftgen_v_1))) - 1)) = reftgen_v_1)))
