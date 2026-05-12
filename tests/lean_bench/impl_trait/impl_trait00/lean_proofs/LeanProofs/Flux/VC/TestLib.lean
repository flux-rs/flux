import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestLib := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, 
 (((k0 10))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((k1 a'₀))) ∧
 (∀ (a'₁ : Int),
  ((k1 a'₁)) ->
   (1 ≤ a'₁))
 
end F
