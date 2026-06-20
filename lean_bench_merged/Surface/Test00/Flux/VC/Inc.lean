import Surface.Test00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Inc := 
 ∀ (x₀ : Int),
  ((x₀ + 1) > x₀)
end F
