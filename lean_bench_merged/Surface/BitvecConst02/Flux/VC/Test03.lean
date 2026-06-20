import Surface.BitvecConst02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test03 := 
 ∀ (x₀ : Int),
  ((x₀ + 3) = (x₀ + (1 + 2)))
end F
