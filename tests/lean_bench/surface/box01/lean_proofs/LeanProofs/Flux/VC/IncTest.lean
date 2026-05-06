import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def IncTest := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (((k0 n₀ n₀))) ∧
  (∀ (b0₀ : Int),
   ((k0 b0₀ n₀)) ->
    ((b0₀ + 1) = (n₀ + 1)))
  
end F
