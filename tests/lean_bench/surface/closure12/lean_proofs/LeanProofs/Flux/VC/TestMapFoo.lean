import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestMapFoo := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   (0 < (v₀ + 1))
end F
