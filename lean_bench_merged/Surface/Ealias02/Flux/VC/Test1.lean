import Surface.Ealias02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   (0 ≤ (v₀ + 1))
end F
