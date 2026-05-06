import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test3 := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k1 : (a0 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k6 : (a0 : Prop) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  (((k0 1 b₀))) ∧
  (((k1 b₀))) ∧
  (((k2 2 b₀))) ∧
  (∀ (a'₁ : Int),
   ((k0 a'₁ b₀)) ->
    ((k3 a'₁ b₀))) ∧
  (∀ (a'₂ : Int),
   ((k3 a'₂ b₀)) ->
    ((k0 a'₂ b₀))) ∧
  (∀ (a'₃ : Int),
   ((k0 a'₃ b₀)) ->
    ((k4 a'₃ b₀))) ∧
  (((k1 b₀)) ->
   ((¬b₀) ->
    ∀ (a'₄ : Int),
     ((k4 a'₄ b₀)) ->
      ∀ (a'₅ : Int),
       ((k2 a'₅ b₀)) ->
        ((a'₄ + a'₅) > 0)) ∧
   (b₀ ->
    (∀ (a'₆ : Int),
     ((k4 a'₆ True)) ->
      ∀ (a'₇ : Int),
       ((k2 a'₇ True)) ->
        (((k5 a'₇ True a'₆ a'₇))) ∧
        (((k6 True))) ∧
        (∀ (a'₈ : Int),
         ((k5 a'₈ True a'₆ a'₇)) ->
          ((k7 a'₈ True))) ∧
        (∀ (a'₉ : Int),
         ((k5 a'₉ True a'₆ a'₇)) ->
          ((k8 a'₉ True))) ∧
        (∀ (a'₁₀ : Int),
         ((k8 a'₁₀ True)) ->
          ((k5 a'₁₀ True a'₆ a'₇))) ∧
        (((k9 a'₆ True)))
        ) ∧
    (((k6 True)) ->
     ∀ (a'₁₁ : Int),
      ((k8 a'₁₁ True)) ->
       (((k8 (a'₁₁ + 1) True))) ∧
       (∀ (a'₁₂ : Int),
        ((k7 a'₁₂ True)) ->
         ((k2 a'₁₂ True))) ∧
       (∀ (a'₁₃ : Int),
        ((k8 a'₁₃ True)) ->
         ((k3 a'₁₃ True))) ∧
       (∀ (a'₁₄ : Int),
        ((k3 a'₁₄ True)) ->
         ((k8 a'₁₄ True))) ∧
       (∀ (a'₁₅ : Int),
        ((k9 a'₁₅ True)) ->
         ((k4 a'₁₅ True)))
       )
    )
   )
  
end F
