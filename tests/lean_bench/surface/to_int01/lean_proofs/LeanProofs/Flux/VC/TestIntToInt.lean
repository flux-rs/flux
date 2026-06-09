import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestIntToInt := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (x₀ = x₀)
end F
