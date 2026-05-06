import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#5}MIN
import LeanFixpoint
open Classical

namespace F



def TestCheckedNegIsize := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (-5)) ->
   ((k0 a'₀))) ∧
 (((5 > num_{impl#5}_MIN) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = (-5)) = True)) ∧
   (∀ (a'₂ : Int),
    (a'₂ = (-0)) ->
     ((k1 a'₂ a'₁))) ∧
   (((0 > num_{impl#5}_MIN) = True)) ∧
   (∀ (a'₃ : Int),
    ((k1 a'₃ a'₁)) ->
     (((a'₃ = 0) = True)) ∧
     (((¬((-9223372036854775808) > num_{impl#5}_MIN)) = True))
     )
   )
 
end F
