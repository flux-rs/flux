import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestBvExtensions := 
 ((BitVec.toNat (BitVec.zeroExtend 32 (BitVec.ofInt 32 4294967295))) ≥ 0) ->
  ((((BitVec.toNat (BitVec.zeroExtend 32 (BitVec.ofInt 32 4294967295))) = 4294967295) = True)) ∧
  (((BitVec.toNat (BitVec.signExtend 32 (BitVec.ofInt 32 4294967295))) ≥ 0) ->
   (((BitVec.toNat (BitVec.signExtend 32 (BitVec.ofInt 32 4294967295))) = 18446744073709551615) = True))
  
end F
