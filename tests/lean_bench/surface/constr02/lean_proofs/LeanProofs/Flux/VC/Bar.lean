import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Bar := 
 ∀ (a₀ : Int),
  ∀ (a'₀ : Int),
   ((0 < a₀) ∧ (a'₀ = a₀)) ->
    (0 < a'₀)
end F
