import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k1 : (a0 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  ((¬b₀) ->
   (((k0 1 b₀))) ∧
   (((k1 b₀))) ∧
   (((k2 1 b₀))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁ b₀)) ->
     ((k3 a'₁ b₀))) ∧
   (∀ (a'₂ : Int),
    ((k0 a'₂ b₀)) ->
     ((k4 a'₂ b₀))) ∧
   (∀ (a'₃ : Int),
    ((k4 a'₃ b₀)) ->
     ((k0 a'₃ b₀)))
   ) ∧
  (b₀ ->
   (((k5 1 True))) ∧
   (((k1 True))) ∧
   (∀ (a'₄ : Int),
    ((k5 a'₄ True)) ->
     ((k2 a'₄ True))) ∧
   (((k3 1 True))) ∧
   (∀ (a'₅ : Int),
    ((k5 a'₅ True)) ->
     ((k4 a'₅ True))) ∧
   (∀ (a'₆ : Int),
    ((k4 a'₆ True)) ->
     ((k5 a'₆ True)))
   ) ∧
  (((k1 b₀)) ->
   ∀ (a'₇ : Int),
    ((k4 a'₇ b₀)) ->
     (((k4 (a'₇ + 1) b₀))) ∧
     (∀ (a'₈ : Int),
      ((k2 a'₈ b₀)) ->
       ∀ (a'₉ : Int),
        ((k3 a'₉ b₀)) ->
         ((a'₈ + a'₉) > 0))
     )
  
end F
