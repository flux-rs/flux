import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 42))) ∧
 (∀ (v₀ : Int),
  ((k0 v₀)) ->
   ((v₀ = 42) = True))
 
end F
