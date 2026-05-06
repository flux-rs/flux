import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def FillVecMap := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (n₀ : Int),
   ∀ (f₀ : Int),
    (n₀ ≥ 0) ->
     (((k0 f₀ n₀ f₀))) ∧
     (∀ (a'₁ : Int),
      ((k1 a'₁ n₀ f₀)) ->
       (a'₁ ≥ 0) ->
        (False ->
         (c0)) ∧
        (∀ (a'₂ : Int),
         ((k0 a'₂ n₀ f₀)) ->
          ((k2 a'₂ n₀ f₀ a'₁))) ∧
        (∀ (a'₃ : Int),
         ((k2 a'₃ n₀ f₀ a'₁)) ->
          ((k0 a'₃ n₀ f₀)))
        ) ∧
     (∀ (item₀ : Int),
      ((0 ≤ item₀) ∧ (item₀ < n₀)) ->
       ((k1 item₀ n₀ f₀))) ∧
     (∀ (a'₅ : Int),
      ((k0 a'₅ n₀ f₀)) ->
       ((k3 a'₅ n₀ f₀))) ∧
     (∀ (a'₆ : Int),
      ((k3 a'₆ n₀ f₀)) ->
       ((k0 a'₆ n₀ f₀))) ∧
     (∀ (a'₇ : Int),
      ((k3 a'₇ n₀ f₀))) ∧
     (∀ (v₀ : Int),
      (v₀ = (n₀ - 0)) ->
       (0 ≤ v₀) ->
        ∀ (a'₉ : Int),
         ((k0 a'₉ n₀ f₀)) ->
          (v₀ = n₀))
     
end F
