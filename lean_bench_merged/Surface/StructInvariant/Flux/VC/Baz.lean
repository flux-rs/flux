import Surface.StructInvariant.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Baz := 
 ∀ (s₀ : Int),
  (s₀ > 10) ->
   (9 < s₀)
end F
