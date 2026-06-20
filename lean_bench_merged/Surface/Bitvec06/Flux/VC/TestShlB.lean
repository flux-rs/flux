import Surface.Bitvec06.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestShlB := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 1#8) ->
   ((BitVec_shiftLeft x₀ 2#8) = 4#8)
end F
