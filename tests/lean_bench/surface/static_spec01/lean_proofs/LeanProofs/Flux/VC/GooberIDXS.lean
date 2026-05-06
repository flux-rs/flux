import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def GooberIDXS := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 0))) ∧
 (((k0 1))) ∧
 (((k0 2))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (a'₀ < 5))
 
end F
