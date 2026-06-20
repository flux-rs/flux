import Surface.LocalPtr00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def ClientSafe := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   (0 ≤ (v₀ + 1))
end F
