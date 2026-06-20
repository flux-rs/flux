import Surface.ToInt01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestBoolToInt := 
 ∀ (x₀ : Prop),
  ((if x₀ then 1 else 0) = (if x₀ then 1 else 0))
end F
