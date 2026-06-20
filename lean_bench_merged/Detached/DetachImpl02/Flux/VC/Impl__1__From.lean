import Detached.DetachImpl02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__1__From := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((n₀ ≠ 0) ->
    (((n₀ - 1) ≥ 0)) ∧
    ((0 ≤ (n₀ - 1)) ->
     (0 ≤ ((n₀ - 1) + 1)) ->
      (((n₀ - 1) + 1) = n₀))
    ) ∧
   ((¬(n₀ ≠ 0)) ->
    (0 = n₀))
   
end F
