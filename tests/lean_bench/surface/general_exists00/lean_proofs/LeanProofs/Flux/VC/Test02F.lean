import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test02F := 
 ∀ (a₀ : Int),
  (a₀ > 0) ->
   (a₀ ≥ 0)
end F
