import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test4 := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   (0 ≤ (v₀ + 1))
end F
