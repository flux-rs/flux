import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestShrA := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 4#8) ->
   ((BitVec_ushiftRight x₀ 2#8) = 1#8)
end F
