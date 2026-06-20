import Surface.Constr03.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (n₀ > 0) ->
    (0 < n₀)
end F
