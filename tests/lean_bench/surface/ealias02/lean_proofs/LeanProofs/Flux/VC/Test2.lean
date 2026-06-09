import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := 
 ∀ (v₀ : Int),
  (10 ≤ v₀) ->
   ((v₀ + 1) ≥ 10)
end F
