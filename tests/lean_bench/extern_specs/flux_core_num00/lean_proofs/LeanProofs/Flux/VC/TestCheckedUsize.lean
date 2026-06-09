import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl11MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestCheckedUsize := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((18446744073709551615 - 1) ≥ 0)) ∧
 (∀ (a'₀ : Int),
  (a'₀ = ((18446744073709551615 - 1) + 1)) ->
   ((k0 a'₀))) ∧
 (((((18446744073709551615 - 1) + 1) ≤ num_impl_11_MAX) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0) ->
    (((a'₁ = 18446744073709551615) = True)) ∧
    (((¬((18446744073709551615 + 1) ≤ num_impl_11_MAX)) = True)) ∧
    (∀ (a'₂ : Int),
     (a'₂ = (5 - 3)) ->
      ((k1 a'₂ a'₁))) ∧
    (∀ (a'₃ : Int),
     ((k1 a'₃ a'₁)) ->
      (a'₃ ≥ 0) ->
       ((a'₃ = 2) = True))
    )
 
end F
