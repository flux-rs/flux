import Surface.Loop00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Prop) -> Prop, 
 ∀ (k₀ : Int),
  (0 ≤ k₀) ->
   (((k0 k₀ k₀))) ∧
   (∀ (k₁ : Int),
    ((k0 k₁ k₀)) ->
     ∀ (a'₁ : Prop),
      ((¬a'₁) ->
       ((k1 k₀ k₁ a'₁))) ∧
      (a'₁ ->
       ((¬(k₁ < (2147483647 - 1))) ->
        ((k1 k₀ k₁ True))) ∧
       ((k₁ < (2147483647 - 1)) ->
        ((k0 (k₁ + 1) k₀)))
       ) ∧
      (((k1 k₀ k₁ a'₁)) ->
       (((k2 k₁ k₀ k₁ a'₁))) ∧
       (∀ (k₂ : Int),
        ((k2 k₂ k₀ k₁ a'₁)) ->
         ((¬(k₂ > 0)) ->
          (k₂ = 0)) ∧
         ((k₂ > 0) ->
          ((k2 (k₂ - 1) k₀ k₁ a'₁)))
         )
       )
      )
   
end F
