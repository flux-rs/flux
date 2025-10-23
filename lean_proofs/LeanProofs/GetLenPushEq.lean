import LeanProofs.Defs
import LeanProofs.InferredInstance
def get_len_push_eq := (∀ (reftgen_elems_0 : ISeq), (∀ (reftgen_v_1 : Int), ((svec_iseq_get (svec_iseq_append reftgen_elems_0 (svec_iseq_singleton reftgen_v_1)) (svec_iseq_len reftgen_elems_0)) = reftgen_v_1)))
