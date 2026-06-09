import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Arr := 
 ∀ (v₀ : Int),
  (v₀ > 0) ->
   (v₀ ≥ 0)
end F
