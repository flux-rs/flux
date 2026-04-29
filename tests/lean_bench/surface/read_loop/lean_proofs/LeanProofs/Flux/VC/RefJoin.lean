import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def RefJoin := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> Prop, 
 ∀ (b₀ : Prop),
  (((k0 0 b₀))) ∧
  (∀ (r₀ : Int),
   ((k0 r₀ b₀)) ->
    ((¬b₀) ->
     (((r₀ + 1) > 0) = True)) ∧
    (b₀ ->
     (((k1 1 True r₀))) ∧
     (∀ (r₁ : Int),
      ((k1 r₁ True r₀)) ->
       ((k0 r₁ True)))
     )
    )
  
end F
