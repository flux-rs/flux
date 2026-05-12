import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__0__TryInto := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (s₀ : Int),
  (((k0 s₀ s₀))) ∧
  (∀ (a'₀ : Int),
   ((k0 a'₀ s₀)) ->
    (a'₀ = s₀))
  
end F
