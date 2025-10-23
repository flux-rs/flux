import LeanProofs.EmptyLen
import LeanProofs.InstanceTheorems
def empty_len_proof : empty_len := by
  unfold empty_len
  intros elems _ elems_empty
  rw [vseq_len_len, elems_empty, vseq_empty_empty]
  rfl
