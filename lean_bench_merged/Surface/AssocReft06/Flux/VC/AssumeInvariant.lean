import Surface.AssocReft06.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def AssumeInvariant := 
 ∀ (s₀ : Int),
  (s₀ > 0) ->
   ((s₀ > 0) = True)
end F
