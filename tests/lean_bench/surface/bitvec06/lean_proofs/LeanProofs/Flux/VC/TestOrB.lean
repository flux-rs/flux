import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestOrB := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 4#8) ->
   ((BitVec.or x₀ 3#8) = 7#8)
end F
