import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestDiv := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ∀ (a'₀ : Int),
    (True -> (a'₀ = (x₀ / 2))) ->
     (a'₀ = (x₀ / 2))
end F
