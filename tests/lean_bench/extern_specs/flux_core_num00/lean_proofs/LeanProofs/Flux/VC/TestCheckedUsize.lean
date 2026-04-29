import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#11}MAX
import LeanFixpoint
open Classical

namespace F



def TestCheckedUsize := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((18446744073709551615 - 1) ≥ 0)) ∧
 (∀ (a'₀ : Int),
  (a'₀ = ((18446744073709551615 - 1) + 1)) ->
   ((k0 a'₀))) ∧
 (((((18446744073709551615 - 1) + 1) ≤ num_{impl#11}_MAX) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0) ->
    (((a'₁ = 18446744073709551615) = True)) ∧
    (((¬((18446744073709551615 + 1) ≤ num_{impl#11}_MAX)) = True)) ∧
    (∀ (a'₂ : Int),
     (a'₂ = (5 - 3)) ->
      ((k1 a'₂ a'₁))) ∧
    (∀ (a'₃ : Int),
     ((k1 a'₃ a'₁)) ->
      (a'₃ ≥ 0) ->
       ((a'₃ = 2) = True))
    )
 
end F
