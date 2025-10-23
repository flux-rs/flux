import LeanProofs.Defs
import LeanProofs.InferredInstance
def push_pop_eq := (∀ (reftgen_elems_0 : ISeq), (∀ (reftgen_v_1 : Int), ((svec_iseq_get (svec_iseq_append reftgen_elems_0 (svec_iseq_singleton reftgen_v_1)) ((svec_iseq_len (svec_iseq_append reftgen_elems_0 (svec_iseq_singleton reftgen_v_1))) - 1)) = reftgen_v_1)))
