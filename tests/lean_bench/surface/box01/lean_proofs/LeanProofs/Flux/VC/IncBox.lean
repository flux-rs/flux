import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def IncBox := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (((k0 (n₀ + 1) n₀))) ∧
  (∀ (a'₀ : Int),
   ((k0 a'₀ n₀)) ->
    (a'₀ = (n₀ + 1)))
  
end F
