import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Maximum := ∃ k0 : (a0 : Int) -> (a1 : (Int -> Prop)) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (Int -> Prop)) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : (Int -> Prop)) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : (Int -> Prop)) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : (Int -> Prop)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : (Int -> Prop)) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (p₀ : (Int -> Prop)),
  ∀ (init₀ : Int),
   (p₀ init₀) ->
    (∀ (v₀ : Int),
     (p₀ v₀) ->
      ((k0 v₀ p₀ init₀))) ∧
    (((k1 init₀ p₀ init₀))) ∧
    (∀ (a'₁ : Int),
     ((k0 a'₁ p₀ init₀)) ->
      ((k2 a'₁ init₀ p₀ init₀))) ∧
    (∀ (max₀ : Int),
     ((k1 max₀ p₀ init₀)) ->
      (∀ (a'₃ : Int),
       ((k2 a'₃ max₀ p₀ init₀)) ->
        ((k3 a'₃ p₀ init₀ max₀))) ∧
      ((p₀ max₀)) ∧
      (∀ (a'₄ : Int),
       ((k3 a'₄ p₀ init₀ max₀)) ->
        (((k4 a'₄ p₀ init₀ max₀ a'₄))) ∧
        (∀ (a'₅ : Int),
         ((k3 a'₅ p₀ init₀ max₀)) ->
          ((k5 a'₅ a'₄ p₀ init₀ max₀ a'₄))) ∧
        (((k4 max₀ p₀ init₀ max₀ a'₄))) ∧
        (∀ (a'₆ : Int),
         ((k3 a'₆ p₀ init₀ max₀)) ->
          ((k5 a'₆ max₀ p₀ init₀ max₀ a'₄))) ∧
        (∀ (max₁ : Int),
         ((k4 max₁ p₀ init₀ max₀ a'₄)) ->
          (((k1 max₁ p₀ init₀))) ∧
          (∀ (a'₈ : Int),
           ((k5 a'₈ max₁ p₀ init₀ max₀ a'₄)) ->
            ((k2 a'₈ max₁ p₀ init₀)))
          )
        )
      )
    
end F
