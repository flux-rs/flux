import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Bar := 
 ∀ (n₀ : Int),
  (42 = n₀) ->
   ((n₀ = 42) = True)
end F
