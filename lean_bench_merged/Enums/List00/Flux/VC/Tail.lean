import Enums.List00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Tail := 
 ∀ (n₀ : Int),
  (0 < n₀) ->
   (n₀ ≥ 0) ->
    (n₀ = 0) ->
     False
end F
