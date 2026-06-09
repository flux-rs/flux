import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def I64U32Lossless := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (True -> (a'₀ = 42)) ->
    (a'₀ = 42)
end F
