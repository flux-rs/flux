import LeanProofs.PushPopEq
import LeanProofs.InstanceTheorems

def push_pop_eq_proof : push_pop_eq := by
  unfold push_pop_eq
  intros elems v
  rw [
    vseq_singleton_singleton,
    vseq_len_len,
    vseq_append_append,
    vseq_get_get
  ]
  unfold list_get
  simp
  intros h
  omega
