import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def RealExample := ∃ k0 : (a0 : BitVec 32) -> (a1 : BitVec 32) -> Prop, 
 ∀ (x₀ : BitVec 32),
  ∀ (y₀ : BitVec 32),
   ((¬(BitVec.ule x₀ (BitVec.ofInt 32 10))) ->
    ((k0 x₀ y₀))) ∧
   ((BitVec.ule x₀ (BitVec.ofInt 32 10)) ->
    ((¬(BitVec_uge y₀ (BitVec.ofInt 32 20))) ->
     ((k0 x₀ y₀))) ∧
    ((BitVec_uge y₀ (BitVec.ofInt 32 20)) ->
     (¬(BitVec.ult x₀ (BitVec.ofInt 32 11))) ->
      ((k0 x₀ y₀)))
    ) ∧
   (((k0 x₀ y₀)) ->
    (False = ((((BitVec.ule x₀ (BitVec.ofInt 32 10)) ∧ (BitVec_uge y₀ (BitVec.ofInt 32 20))) ∧ (BitVec.ult x₀ (BitVec.ofInt 32 11))) ∧ (BitVec_ugt y₀ (BitVec.ofInt 32 21)))))
   
end F
