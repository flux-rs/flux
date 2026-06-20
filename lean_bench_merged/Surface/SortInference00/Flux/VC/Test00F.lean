import Surface.SortInference00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test00F := 
 ∀ (b₀ : Int),
  ∀ (a₀ : Int),
   (b₀ > a₀) ->
    ((b₀ - a₀) > 0)
end F
