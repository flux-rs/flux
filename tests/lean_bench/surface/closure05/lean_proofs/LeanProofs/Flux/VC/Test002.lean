import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test002 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (f₀ : Int),
   (∀ (a'₁ : Int),
    ((k0 a'₁ f₀)) ->
     ∀ (a'₂ : Int),
      ((k1 a'₂ f₀)) ->
       ∀ (a'₃ : Int),
        ((k2 a'₃ f₀)) ->
         ((0 ≤ a'₂)) ∧
         ((0 ≤ a'₃)) ∧
         (∀ (a'₄ : Int),
          ((k0 a'₄ f₀)) ->
           ∀ (a'₅ : Int),
            ((k1 a'₅ f₀)) ->
             ∀ (a'₆ : Int),
              ((k2 a'₆ f₀)) ->
               ((0 ≤ a'₅)) ∧
               ((0 ≤ a'₆)) ∧
               (∀ (v₀ : Int),
                (10 ≤ v₀) ->
                 ((k3 v₀ f₀)))
               )
         ) ∧
   (False ->
    (c0)) ∧
   (((k0 f₀ f₀))) ∧
   (((k1 99 f₀))) ∧
   (((k2 100 f₀))) ∧
   (∀ (a'₈ : Int),
    ((k3 a'₈ f₀)) ->
     (0 ≤ a'₈))
   
end F
