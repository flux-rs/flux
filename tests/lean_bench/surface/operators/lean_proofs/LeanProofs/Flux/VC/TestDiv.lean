import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestDiv := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ∀ (a'₀ : Int),
    (True -> (a'₀ = (x₀ / 2))) ->
     (a'₀ = (x₀ / 2))
end F
