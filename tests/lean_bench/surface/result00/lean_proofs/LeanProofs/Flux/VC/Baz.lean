import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Baz := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 0))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (a'₀ = 0))
 
end F
