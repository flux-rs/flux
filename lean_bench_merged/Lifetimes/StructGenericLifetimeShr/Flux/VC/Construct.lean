import Lifetimes.StructGenericLifetimeShr.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Construct := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ((x₀ + 1) > 0)
end F
