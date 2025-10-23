import LeanProofs.PushPopEq
import LeanProofs.InstanceTheorems

def push_pop_eq_proof : push_pop_eq := by
  unfold push_pop_eq
  intros elems v
  rw [
    iseq_singleton_singleton,
    iseq_len_len,
    iseq_append_append,
    iseq_get_get
  ]
  unfold list_get
  simp
  intros h
  omega
