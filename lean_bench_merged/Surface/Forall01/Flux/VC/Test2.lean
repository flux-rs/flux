import Surface.Forall01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (a'₀ > (-1))
end F
