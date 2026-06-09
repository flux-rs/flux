import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestFirstBranch := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (a'₀ > 0) ->
    ((a'₀ ≠ 0) = True)
end F
