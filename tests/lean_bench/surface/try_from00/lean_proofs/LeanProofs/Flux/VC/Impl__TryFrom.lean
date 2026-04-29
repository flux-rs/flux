import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__TryFrom := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (x₀ : Int),
  (((k0 x₀ x₀))) ∧
  (∀ (a'₀ : Int),
   ((k0 a'₀ x₀)) ->
    (x₀ = a'₀))
  
end F
