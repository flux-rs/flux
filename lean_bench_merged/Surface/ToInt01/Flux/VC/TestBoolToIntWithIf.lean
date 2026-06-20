import Surface.ToInt01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestBoolToIntWithIf := 
 ∀ (x₀ : Prop),
  ((¬x₀) ->
   (0 = (if x₀ then 1 else 0))) ∧
  (x₀ ->
   (1 = (if True then 1 else 0)))
  
end F
