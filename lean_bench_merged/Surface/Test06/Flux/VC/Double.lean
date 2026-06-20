import Surface.Test06.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Double := 
 ∀ (x₀ : Int),
  (0 < x₀) ->
   (x₀ < (x₀ + x₀))
end F
