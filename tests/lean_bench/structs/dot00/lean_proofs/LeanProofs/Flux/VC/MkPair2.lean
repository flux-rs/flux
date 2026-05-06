import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def MkPair2 := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   ((a₀ = a₀)) ∧
   ((b₀ = b₀))
   
end F
