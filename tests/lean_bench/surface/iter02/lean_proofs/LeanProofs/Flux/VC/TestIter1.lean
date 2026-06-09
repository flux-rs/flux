import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.SliceIterIter
open Classical
set_option linter.unusedVariables false


namespace F



def TestIter1 := 
 ∀ (n₀ : Int),
  (n₀ > 0) ->
   (n₀ ≥ 0) ->
    ∀ (next_s₀ : SliceIterIter),
     (((0 + 1) = (SliceIterIter.idx next_s₀)) ∧ (n₀ = (SliceIterIter.len next_s₀))) ->
      ((0 < n₀) = True)
end F
