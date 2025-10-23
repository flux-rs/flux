import LeanProofs.GetLenPushEq
import LeanProofs.InstanceTheorems

def get_len_push_eq_proof : get_len_push_eq := by
  unfold get_len_push_eq
  intros elems v
  rw [
    iseq_get_get,
    iseq_append_append,
    iseq_singleton_singleton,
    iseq_len_len
  ]
  unfold list_get
  simp
  omega
