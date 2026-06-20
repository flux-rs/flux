import Surface.Char03.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def CastToU8AndBack := 
 ∀ (x₀ : Int),
  (x₀ < 256) ->
   (x₀ ≤ 1114111) ->
    (0 ≤ x₀) ->
     ∀ (a'₀ : Int),
      (a'₀ ≥ 0) ->
       ((x₀ ≤ 255) -> (a'₀ = x₀)) ->
        (a'₀ = x₀)
end F
