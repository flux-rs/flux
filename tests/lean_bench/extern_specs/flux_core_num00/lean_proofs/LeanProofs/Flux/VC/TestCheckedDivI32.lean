import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl2MIN
import LeanFixpoint
open Classical

namespace F



def TestCheckedDivI32 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (10 / 2)) ->
   ((k0 a'₀))) ∧
 ((((10 ≠ num_impl_2_MIN) ∨ (2 ≠ (-1))) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 5) = True)) ∧
   (∀ (a'₂ : Int),
    (a'₂ = (-((-(-10)) / 3))) ->
     ((k1 a'₂ a'₁))) ∧
   (((((-10) ≠ num_impl_2_MIN) ∨ (3 ≠ (-1))) = True)) ∧
   (∀ (a'₃ : Int),
    ((k1 a'₃ a'₁)) ->
     (((a'₃ = (-3)) = True)) ∧
     (((¬(((-2147483648) ≠ num_impl_2_MIN) ∨ ((-1) ≠ (-1)))) = True))
     )
   )
 
end F
