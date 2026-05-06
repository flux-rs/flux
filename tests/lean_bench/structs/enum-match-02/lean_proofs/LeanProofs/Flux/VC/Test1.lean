import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test1 := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 (5 + 7)))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (0 ≤ a'₀))
 
end F
