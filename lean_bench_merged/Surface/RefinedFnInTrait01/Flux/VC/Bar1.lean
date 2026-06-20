import Surface.RefinedFnInTrait01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Bar1 := ∃ k0 : (a0 : Int) -> (a1 : (Int -> Prop)) -> (a2 : Int) -> Prop, 
 ∀ (q₀ : (Int -> Prop)),
  ∀ (v₀ : Int),
   (q₀ v₀) ->
    (((k0 v₀ q₀ v₀))) ∧
    (∀ (v₁ : Int),
     ((k0 v₁ q₀ v₀)) ->
      (q₀ v₁))
    
end F
