import LeanProofs.PushLenEqPlusOne
import LeanProofs.InstanceTheorems
def push_len_eq_plus_one_proof : push_len_eq_plus_one := by
  unfold push_len_eq_plus_one
  intros elems v
  rw [
    vseq_len_len,
    vseq_len_len,
    vseq_append_append,
    vseq_singleton_singleton
  ]
  simp
