import Surface.Real00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := 
 ∀ (x₀ : Real),
  ((x₀ + 1.0) > x₀)
end F
