import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__Eq := 
 ∀ (lhs₀ : Int),
  ∀ (rhs₀ : Int),
   ((lhs₀ = rhs₀) = (lhs₀ = rhs₀))
end F
