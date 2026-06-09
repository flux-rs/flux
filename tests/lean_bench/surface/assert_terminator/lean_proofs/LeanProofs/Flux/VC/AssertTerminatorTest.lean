import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def AssertTerminatorTest := 
 ∀ (v₀ : Int),
  ∀ (a₀ : Int),
   (v₀ > 0) ->
    (a₀ ≥ 0) ->
     (v₀ ≥ 0) ->
      (v₀ ≠ 0)
end F
