import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def IsSomeFlip := ∃ k0 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  ((b₀ = False) ->
   ((k0 False False b₀))) ∧
  ((b₀ = True) ->
   ∀ (a'₀ : Int),
    ((k0 True True b₀))) ∧
  (∀ (a'₁ : Prop),
   ∀ (x₀ : Prop),
    ((k0 a'₁ x₀ b₀)) ->
     (a'₁ = b₀))
  
end F
