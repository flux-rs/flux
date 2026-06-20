import Surface.ParamUnderMutRef.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Baz := 
 ∀ (v₀ : Int),
  (v₀ > 0) ->
   ((v₀ + 1) > 0)
end F
