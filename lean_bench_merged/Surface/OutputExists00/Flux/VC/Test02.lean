import Surface.OutputExists00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test02 := 
 ∀ (n₀ : Int),
  ∀ (v₀ : Int),
   (v₀ > n₀) ->
    ((v₀ - n₀) > 0)
end F
