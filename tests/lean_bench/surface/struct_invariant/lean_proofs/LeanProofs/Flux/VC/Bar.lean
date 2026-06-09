import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Bar := 
 ∀ (z₀ : Int),
  (99 < z₀) ->
   (z₀ > 10)
end F
