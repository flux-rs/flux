import ExternSpecs.FluxCoreSlice00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestRangeIndexInBounds := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (a'₀ > 10) ->
    (1 ≤ a'₀)
end F
