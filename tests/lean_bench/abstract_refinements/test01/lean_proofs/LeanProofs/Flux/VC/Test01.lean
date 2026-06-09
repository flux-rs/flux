import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   (a₀ < b₀) ->
    ((b₀ - a₀) > 0)
end F
