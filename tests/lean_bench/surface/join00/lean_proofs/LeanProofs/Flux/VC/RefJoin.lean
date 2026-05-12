import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def RefJoin := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  ((¬b₀) ->
   ((k0 2 b₀))) ∧
  (b₀ ->
   ((k0 1 True))) ∧
  (∀ (r₀ : Int),
   ((k0 r₀ b₀)) ->
    ((r₀ > 0) = True))
  
end F
