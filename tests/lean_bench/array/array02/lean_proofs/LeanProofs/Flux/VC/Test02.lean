import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test02 := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 42))) ∧
 (((k0 42))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (a'₀ ≥ 0))
 
end F
