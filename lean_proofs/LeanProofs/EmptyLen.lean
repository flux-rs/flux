import LeanProofs.Defs
import LeanProofs.InferredInstance
def empty_len := (∀ (reftgen_elems_0 : (VSeq Int)), (∀ (__ : Int), ((reftgen_elems_0 = (svec_vseq_empty )) -> ((svec_vseq_len reftgen_elems_0) = 0))))
