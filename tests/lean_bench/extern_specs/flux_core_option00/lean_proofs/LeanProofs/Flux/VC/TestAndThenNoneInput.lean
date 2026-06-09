import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAndThenNoneInput := 
 ∀ (s₀ : Prop),
  (s₀ -> False) ->
   ((¬s₀) = True)
end F
