import Surface.Closure04.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test001 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (frog₀ : Int),
   (∀ (a'₁ : Int),
    ((k0 a'₁ frog₀)) ->
     ∀ (a'₂ : Int),
      ((k1 a'₂ frog₀)) ->
       ((0 ≤ a'₂)) ∧
       (∀ (a'₃ : Int),
        ((k0 a'₃ frog₀)) ->
         ∀ (a'₄ : Int),
          ((k1 a'₄ frog₀)) ->
           ((0 ≤ a'₄)) ∧
           (∀ (v₀ : Int),
            (0 ≤ v₀) ->
             ((k2 v₀ frog₀)))
           )
       ) ∧
   (False ->
    ((c0) ∨ False)) ∧
   (((k0 frog₀ frog₀))) ∧
   (((k1 99 frog₀))) ∧
   (∀ (a'₆ : Int),
    ((k2 a'₆ frog₀)) ->
     (0 ≤ a'₆))
   
end F
