import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestIndexAfterIsEmpty := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (a'₀ ≠ 0) ->
    (0 < a'₀)
end F
