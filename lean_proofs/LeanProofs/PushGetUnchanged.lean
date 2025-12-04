import LeanProofs.Defs
import LeanProofs.InferredInstance
def push_get_unchanged := (∀ (reftgen_elems_0 : (VSeq Int)), (∀ (reftgen_v_1 : Int), (∀ (reftgen_i_2 : Int), (∀ (__ : Int), (((0 ≤ reftgen_i_2) ∧ (reftgen_i_2 < (svec_vseq_len reftgen_elems_0))) -> ((svec_vseq_get (svec_vseq_append reftgen_elems_0 (svec_vseq_singleton reftgen_v_1)) reftgen_i_2) = (svec_vseq_get reftgen_elems_0 reftgen_i_2)))))))
