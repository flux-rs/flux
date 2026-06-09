import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := 
 ∀ (x₀ : Int),
  (0 ≤ x₀) ->
   (0 ≤ (x₀ + 1))
end F
