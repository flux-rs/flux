import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test2 := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> Prop, 
 ∀ (b₀ : Prop),
  ∀ (s₀ : Int),
   ((¬b₀) ->
    (s₀ ≥ 0) ->
     ∀ (a'₂ : Int),
      ((k0 s₀ b₀ s₀))) ∧
   (b₀ ->
    ((k0 0 True s₀))) ∧
   (∀ (x₀ : Int),
    ((k0 x₀ b₀ s₀)) ->
     ((x₀ + 1) > 0))
   
end F
