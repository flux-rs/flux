import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Sub := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   (b₀ ≤ a₀) ->
    ((0 ≤ (a₀ - b₀)) = True)
end F
