import LeanProofs.PushGetUnchanged
import LeanProofs.InstanceTheorems

def push_get_unchanged_proof : push_get_unchanged := by
  unfold push_get_unchanged
  intros elems v i _ i_in_range
  rw [
    vseq_get_get,
    vseq_append_append,
    vseq_singleton_singleton,
    vseq_get_get
  ]
  rw [vseq_len_len] at i_in_range
  unfold list_get
  simp_all
  omega
