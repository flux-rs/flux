import ExternSpecs.FluxCoreSlice00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestSplitAtCheckedOutOfBounds := 
 ∀ (a'₀ : Int),
  ∀ (mid₀ : Int),
   (a'₀ ≥ 0) ->
    (mid₀ ≥ 0) ->
     (mid₀ > a'₀) ->
      ((¬(mid₀ ≤ a'₀)) = True)
end F
