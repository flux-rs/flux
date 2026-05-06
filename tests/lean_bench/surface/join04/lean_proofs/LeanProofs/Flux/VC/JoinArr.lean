import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def JoinArr := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k1 : (a0 : Prop) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  ((¬b₀) ->
   (((k0 3 b₀))) ∧
   (((k0 4 b₀))) ∧
   (((k1 b₀))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁ b₀)) ->
     ((k2 a'₁ b₀)))
   ) ∧
  (b₀ ->
   (((k3 1 True))) ∧
   (((k3 2 True))) ∧
   (((k1 True))) ∧
   (∀ (a'₂ : Int),
    ((k3 a'₂ True)) ->
     ((k2 a'₂ True)))
   ) ∧
  (((k1 b₀)) ->
   ∀ (a'₃ : Int),
    ((k2 a'₃ b₀)) ->
     (a'₃ > 0))
  
end F
