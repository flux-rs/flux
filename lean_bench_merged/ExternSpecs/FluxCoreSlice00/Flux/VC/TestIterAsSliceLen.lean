import ExternSpecs.FluxCoreSlice00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestIterAsSliceLen := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   ((a'₀ = a'₀) = True)
end F
