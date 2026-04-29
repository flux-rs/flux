import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def CloseAtJoin := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> Prop, 
 ∀ (b₀ : Prop),
  (((k0 1 b₀))) ∧
  (∀ (x₀ : Int),
   ((k0 x₀ b₀)) ->
    ((¬b₀) ->
     ((k1 x₀ b₀ x₀))) ∧
    (b₀ ->
     ((k1 (x₀ + 1) True x₀))) ∧
    (∀ (x₁ : Int),
     ((k1 x₁ b₀ x₀)) ->
      (x₁ > 0))
    )
  
end F
