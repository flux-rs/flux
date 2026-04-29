import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestSelect := 
 ∀ (guess₀ : Int),
  ∀ (secret₀ : Int),
   (¬(guess₀ ≠ secret₀)) ->
    (guess₀ = secret₀)
end F
