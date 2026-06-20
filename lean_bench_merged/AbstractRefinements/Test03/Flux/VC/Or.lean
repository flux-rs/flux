import AbstractRefinements.Test03.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Or := ∃ k0 : (a0 : Int) -> (a1 : (Int -> Prop)) -> (a2 : (Int -> Prop)) -> Prop, 
 ∀ (p1₀ : (Int -> Prop)),
  ∀ (p2₀ : (Int -> Prop)),
   ∀ (a'₀ : Int),
    (((k0 a'₀ p1₀ p2₀)) ->
     ((p1₀ a'₀) ∨ (p2₀ a'₀))) ∧
    (((p1₀ a'₀) ∨ (p2₀ a'₀)) ->
     ((k0 a'₀ p1₀ p2₀)))
    
end F
