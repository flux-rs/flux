import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl2MIN
open Classical
set_option linter.unusedVariables false


namespace F



def TestCheckedNegI32 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (-5)) ->
   ((k0 a'₀))) ∧
 (((5 > num_impl_2_MIN) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = (-5)) = True)) ∧
   (∀ (a'₂ : Int),
    (a'₂ = (-0)) ->
     ((k1 a'₂ a'₁))) ∧
   (((0 > num_impl_2_MIN) = True)) ∧
   (∀ (a'₃ : Int),
    ((k1 a'₃ a'₁)) ->
     (((a'₃ = 0) = True)) ∧
     (((¬((-2147483648) > num_impl_2_MIN)) = True))
     )
   )
 
end F
