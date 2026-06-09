import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   ((v₀ + 1) ≥ 0)
end F
