import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestSelect := 
 ∀ (guess₀ : Int),
  ∀ (secret₀ : Int),
   (¬(guess₀ ≠ secret₀)) ->
    (guess₀ = secret₀)
end F
