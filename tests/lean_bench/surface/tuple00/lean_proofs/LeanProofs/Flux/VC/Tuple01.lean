import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Tuple01 := 
 ∀ (x₀ : Int),
  ((x₀ - x₀) = 0)
end F
