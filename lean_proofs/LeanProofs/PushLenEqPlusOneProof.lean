import LeanProofs.PushLenEqPlusOne
import LeanProofs.InstanceTheorems
def push_len_eq_plus_one_proof : push_len_eq_plus_one := by
  unfold push_len_eq_plus_one
  intros elems v
  rw [
    iseq_len_len,
    iseq_len_len,
    iseq_append_append,
    iseq_singleton_singleton
  ]
  simp
