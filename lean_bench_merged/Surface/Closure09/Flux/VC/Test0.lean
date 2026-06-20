import Surface.Closure09.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test0 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (f₀ : Int),
   (∀ (a'₁ : Int),
    ((k0 a'₁ f₀)) ->
     ∀ (a'₂ : Int),
      ((k1 a'₂ f₀)) ->
       ∀ (a'₃ : Int),
        ((k0 a'₃ f₀)) ->
         ∀ (a'₄ : Int),
          ((k1 a'₄ f₀)) ->
           ∀ (a'₅ : Int),
            (a'₅ = (a'₄ + 1)) ->
             ((k2 a'₅ f₀))) ∧
   (False ->
    ((c0) ∨ False)) ∧
   (((k0 f₀ f₀))) ∧
   (((k1 99 f₀))) ∧
   (∀ (a'₆ : Int),
    ((k2 a'₆ f₀)) ->
     (a'₆ = 100))
   
end F
