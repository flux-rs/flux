import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def RunClosure := 
 ∀ (c0 : Prop),
  False ->
   ((c0) ∨ False)
end F
