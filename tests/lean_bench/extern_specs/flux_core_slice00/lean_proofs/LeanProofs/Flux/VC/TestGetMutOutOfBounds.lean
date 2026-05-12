import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestGetMutOutOfBounds := 
 ∀ (a'₀ : Int),
  ∀ (i₀ : Int),
   (a'₀ ≥ 0) ->
    (i₀ ≥ 0) ->
     (i₀ ≥ a'₀) ->
      ((¬(i₀ < a'₀)) = True)
end F
