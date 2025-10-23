import LeanProofs.Defs
import LeanProofs.InferredInstance
def push_get_unchanged := (∀ (reftgen_elems_0 : ISeq), (∀ (reftgen_v_1 : Int), (∀ (reftgen_i_2 : Int), (∀ (__ : Int), (((0 ≤ reftgen_i_2) ∧ (reftgen_i_2 < (svec_iseq_len reftgen_elems_0))) -> ((svec_iseq_get (svec_iseq_append reftgen_elems_0 (svec_iseq_singleton reftgen_v_1)) reftgen_i_2) = (svec_iseq_get reftgen_elems_0 reftgen_i_2)))))))
