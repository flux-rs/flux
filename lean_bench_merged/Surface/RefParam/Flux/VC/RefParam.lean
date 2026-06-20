import Surface.RefParam.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def RefParam := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   (((v₀ + 1) > 0) = True)
end F
