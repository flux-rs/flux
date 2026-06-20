import Surface.Bitvec01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def WrapIndex := 
 ∀ (size₀ : Int),
  ∀ (index₀ : Int),
   ((1 ≤ size₀) ∧ ((BitVec.and (BitVec.ofInt 32 size₀) (BitVec.sub (BitVec.ofInt 32 size₀) (BitVec.ofInt 32 1))) = (BitVec.ofInt 32 0))) ->
    (index₀ ≥ 0) ->
     (size₀ ≥ 0) ->
      ((BitVec.toNat (BitVec.and (BitVec.ofInt 32 index₀) (BitVec.sub (BitVec.ofInt 32 size₀) (BitVec.ofInt 32 1)))) ≥ 0) ->
       ((BitVec.toNat (BitVec.and (BitVec.ofInt 32 index₀) (BitVec.sub (BitVec.ofInt 32 size₀) (BitVec.ofInt 32 1)))) < size₀)
end F
