import Surface.RefinedTypeVar01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Baz := ∃ k0 : (a0 : Int) -> (a1 : (Int -> Prop)) -> (a2 : Int) -> Prop, 
 ∀ (q₀ : (Int -> Prop)),
  ∀ (v₀ : Int),
   (q₀ v₀) ->
    (((k0 v₀ q₀ v₀))) ∧
    (∀ (a'₁ : Int),
     ((k0 a'₁ q₀ v₀)) ->
      (q₀ a'₁))
    
end F
