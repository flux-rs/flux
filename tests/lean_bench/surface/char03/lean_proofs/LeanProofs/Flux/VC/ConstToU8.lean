import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def ConstToU8 := 
 (97 ≤ 1114111) ->
  (0 ≤ 97) ->
   ∀ (a'₀ : Int),
    (a'₀ ≥ 0) ->
     ((97 ≤ 255) -> (a'₀ = 97)) ->
      (a'₀ = 97)
end F
