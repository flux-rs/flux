import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestGetOutOfBounds := 
 ∀ (a'₀ : Int),
  ∀ (i₀ : Int),
   (a'₀ ≥ 0) ->
    (i₀ ≥ 0) ->
     (i₀ ≥ a'₀) ->
      ((¬(i₀ < a'₀)) = True)
end F
