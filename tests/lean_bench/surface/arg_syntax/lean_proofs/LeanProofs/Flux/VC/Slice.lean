import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Slice := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   ∀ (v₀ : Int),
    (v₀ > 0) ->
     (v₀ ≥ 0)
end F
