import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test00 := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  ((¬b₀) ->
   ((k0 1 b₀))) ∧
  (b₀ ->
   ((k0 0 True))) ∧
  (∀ (p₀ : Int),
   ((k0 p₀ b₀)) ->
    ((0 + p₀) ≥ 0))
  
end F
