import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test01 := ∃ k0 : (a0 : Int) -> Prop, 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (¬(x₀ ≥ 100)) ->
    (((k0 x₀))) ∧
    (((k0 x₀)) ->
     (x₀ < 100))
    
end F
