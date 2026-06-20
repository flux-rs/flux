import Surface.Alias00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (0 ≤ (n₀ + 1))
end F
