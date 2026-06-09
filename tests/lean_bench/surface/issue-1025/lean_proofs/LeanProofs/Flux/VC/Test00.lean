import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test00 := 
 ∀ (c1 : (Prop -> Prop)),
  ∀ (c0 : (Int -> Prop)),
   ∀ (x₀ : Int),
    ∀ (y₀ : Prop),
     (c0 x₀) ->
      (c1 y₀) ->
       (((x₀ + 1) ≥ (1 + x₀)) = True)
end F
