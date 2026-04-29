import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def BobARR := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 1))) ∧
 (((k0 2))) ∧
 (((k0 3))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (a'₀ < 10))
 
end F
