import LeanProofs.PushGetUnchanged
import LeanProofs.InstanceTheorems

def push_get_unchanged_proof : push_get_unchanged := by
  unfold push_get_unchanged
  intros elems v i _ i_in_range
  rw [
    iseq_get_get,
    iseq_append_append,
    iseq_singleton_singleton,
    iseq_get_get
  ]
  rw [iseq_len_len] at i_in_range
  unfold list_get
  simp_all
  omega
