import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def GenRange := 
 ∀ (lo₀ : Int),
  ∀ (hi₀ : Int),
   (lo₀ < hi₀) ->
    (lo₀ ≥ 0) ->
     (hi₀ ≥ 0) ->
      (lo₀ ≤ lo₀)
end F
