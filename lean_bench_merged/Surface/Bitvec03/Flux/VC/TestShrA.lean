import Surface.Bitvec03.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestShrA := 
 ∀ (x₀ : BitVec 32),
  (x₀ = 8#32) ->
   ((BitVec_ushiftRight x₀ 3#32) = 1#32)
end F
