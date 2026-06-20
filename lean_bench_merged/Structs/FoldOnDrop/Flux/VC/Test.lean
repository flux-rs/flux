import Structs.FoldOnDrop.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := 
 ∀ (s₀ : Int),
  (s₀ ≥ 0) ->
   ((s₀ + 1) ≥ 0)
end F
