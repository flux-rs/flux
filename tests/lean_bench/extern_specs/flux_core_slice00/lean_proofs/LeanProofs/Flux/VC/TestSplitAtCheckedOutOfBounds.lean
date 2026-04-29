import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestSplitAtCheckedOutOfBounds := 
 ∀ (a'₀ : Int),
  ∀ (mid₀ : Int),
   (a'₀ ≥ 0) ->
    (mid₀ ≥ 0) ->
     (mid₀ > a'₀) ->
      ((¬(mid₀ ≤ a'₀)) = True)
end F
