import Surface.Bitvec03.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAndA := 
 ∀ (x₀ : BitVec 32),
  (x₀ = 10#32) ->
   ((BitVec.and x₀ 3#32) = 2#32)
end F
