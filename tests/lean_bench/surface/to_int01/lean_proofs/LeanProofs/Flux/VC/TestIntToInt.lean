import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestIntToInt := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (x₀ = x₀)
end F
