import LeanProofs.EmptyLenZero
import LeanProofs.InstanceTheorems
def empty_len_zero_proof : empty_len_zero := by
  unfold empty_len_zero
  rw [
    iseq_len_len,
    iseq_empty_empty
  ]
  simp
