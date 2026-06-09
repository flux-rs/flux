import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl5MIN
open Classical
set_option linter.unusedVariables false


namespace F



def TestCheckedDivIsize := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (10 / 2)) ->
   ((k0 a'₀))) ∧
 ((((10 ≠ num_impl_5_MIN) ∨ (2 ≠ (-1))) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 5) = True)) ∧
   (∀ (a'₂ : Int),
    (a'₂ = (-((-(-10)) / 3))) ->
     ((k1 a'₂ a'₁))) ∧
   (((((-10) ≠ num_impl_5_MIN) ∨ (3 ≠ (-1))) = True)) ∧
   (∀ (a'₃ : Int),
    ((k1 a'₃ a'₁)) ->
     (((a'₃ = (-3)) = True)) ∧
     (∀ (a'₄ : Int),
      (a'₄ = ((-(-10)) / (-(-3)))) ->
       ((k2 a'₄ a'₁ a'₃))) ∧
     (((((-10) ≠ num_impl_5_MIN) ∨ ((-3) ≠ (-1))) = True)) ∧
     (∀ (a'₅ : Int),
      ((k2 a'₅ a'₁ a'₃)) ->
       (((a'₅ = 3) = True)) ∧
       (∀ (a'₆ : Int),
        (a'₆ = (-(10 / (-(-3))))) ->
         ((k3 a'₆ a'₁ a'₃ a'₅))) ∧
       ((((10 ≠ num_impl_5_MIN) ∨ ((-3) ≠ (-1))) = True)) ∧
       (∀ (a'₇ : Int),
        ((k3 a'₇ a'₁ a'₃ a'₅)) ->
         (((a'₇ = (-3)) = True)) ∧
         (((¬(((-9223372036854775808) ≠ num_impl_5_MIN) ∨ ((-1) ≠ (-1)))) = True))
         )
       )
     )
   )
 
end F
