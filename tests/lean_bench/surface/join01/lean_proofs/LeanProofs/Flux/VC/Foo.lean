import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Foo := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k1 : (a0 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  ((¬b₀) ->
   (((k0 1 b₀))) ∧
   (((k1 b₀))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁ b₀)) ->
     ((k2 a'₁ b₀))) ∧
   (∀ (a'₂ : Int),
    ((k0 a'₂ b₀)) ->
     ((k3 a'₂ b₀))) ∧
   (∀ (a'₃ : Int),
    ((k3 a'₃ b₀)) ->
     ((k0 a'₃ b₀)))
   ) ∧
  (b₀ ->
   (((k1 True))) ∧
   (((k2 1 True))) ∧
   (((k3 0 True))) ∧
   (∀ (a'₄ : Int),
    ((k3 a'₄ True)) ->
     (a'₄ = 0))
   ) ∧
  (((k1 b₀)) ->
   ∀ (a'₅ : Int),
    ((k3 a'₅ b₀)) ->
     ∀ (a'₆ : Int),
      ((k2 a'₆ b₀)) ->
       (a'₅ ≥ 0))
  
end F
