import Surface.Alias05.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := 
 ∀ (v₀ : Int),
  (10 ≤ v₀) ->
   (10 ≤ (v₀ + 1))
end F
