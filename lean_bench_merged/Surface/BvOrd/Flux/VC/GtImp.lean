import Surface.BvOrd.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def GtImp := 
 ∀ (x₀ : BitVec 32),
  ∀ (y₀ : BitVec 32),
   ((BitVec_ugt x₀ y₀) ∧ (BitVec_ugt y₀ (BitVec.ofInt 32 32)) ∧ (BitVec.ult x₀ (BitVec.ofInt 32 255))) ->
    ((BitVec_ugt (BitVec.add x₀ (BitVec.ofInt 32 32)) (BitVec.sub y₀ (BitVec.ofInt 32 32))) = True)
end F
