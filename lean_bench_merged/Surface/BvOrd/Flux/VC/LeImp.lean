import Surface.BvOrd.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def LeImp := 
 ∀ (x₀ : BitVec 32),
  ∀ (y₀ : BitVec 32),
   ((BitVec.ule x₀ y₀) ∧ (BitVec_uge x₀ (BitVec.ofInt 32 32)) ∧ (BitVec.ule y₀ (BitVec.ofInt 32 255))) ->
    ((BitVec.ule (BitVec.sub x₀ (BitVec.ofInt 32 32)) (BitVec.add y₀ (BitVec.ofInt 32 32))) = True)
end F
