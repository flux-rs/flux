import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestSplitAtMutCheckedLengths := 
 ∀ (a'₀ : Int),
  ∀ (mid₀ : Int),
   (a'₀ ≥ 0) ->
    (mid₀ ≥ 0) ->
     ((mid₀ ≤ a'₀) = True) ->
      ((a'₀ - mid₀) ≥ 0) ->
       (((mid₀ = mid₀) = True)) ∧
       ((((a'₀ - mid₀) = (a'₀ - mid₀)) = True))
       
end F
