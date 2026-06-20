import Surface.Closure12.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestMapFoo := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   (0 < (v₀ + 1))
end F
