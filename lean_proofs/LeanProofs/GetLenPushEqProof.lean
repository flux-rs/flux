import LeanProofs.GetLenPushEq
import LeanProofs.InstanceTheorems

def get_len_push_eq_proof : get_len_push_eq := by
  unfold get_len_push_eq
  intros elems v
  rw [
    vseq_get_get,
    vseq_append_append,
    vseq_singleton_singleton,
    vseq_len_len
  ]
  unfold list_get
  simp
  omega
