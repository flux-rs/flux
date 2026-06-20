import Surface.Bitvec06.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestXorA := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 6#8) ->
   ((BitVec.xor x₀ 3#8) = 5#8)
end F
