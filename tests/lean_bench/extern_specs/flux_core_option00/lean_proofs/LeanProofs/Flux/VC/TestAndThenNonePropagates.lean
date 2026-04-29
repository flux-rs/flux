import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestAndThenNonePropagates := 
 ∀ (x₀ : Prop),
  ∀ (result₀ : Prop),
   (result₀ -> x₀) ->
    (¬x₀) ->
     ((¬result₀) = True)
end F
