import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAndB := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 6#8) ->
   ((BitVec.and x₀ 3#8) = 2#8)
end F
