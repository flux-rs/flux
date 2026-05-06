import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def NoCloseJoin := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> Prop, 
 ∀ (b₀ : Prop),
  (((k0 1 b₀))) ∧
  (∀ (x₀ : Int),
   ((k0 x₀ b₀)) ->
    ((¬b₀) ->
     ((k1 ((x₀ + 1) + 2) b₀ x₀))) ∧
    (b₀ ->
     ((k1 ((x₀ + 1) + 1) True x₀))) ∧
    (∀ (a'₂ : Int),
     ((k1 a'₂ b₀ x₀)) ->
      (a'₂ > 2))
    )
  
end F
