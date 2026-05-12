import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Update := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 1))) ∧
 (∀ (x₀ : Int),
  ((k0 x₀)) ->
   ((x₀ + 1) = 2))
 
end F
