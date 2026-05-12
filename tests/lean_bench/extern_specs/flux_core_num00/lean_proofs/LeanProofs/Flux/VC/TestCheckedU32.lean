import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl8MAX
import LeanFixpoint
open Classical

namespace F



def TestCheckedU32 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((4294967295 - 1) ≥ 0)) ∧
 (∀ (a'₀ : Int),
  (a'₀ = ((4294967295 - 1) + 1)) ->
   ((k0 a'₀))) ∧
 (((((4294967295 - 1) + 1) ≤ num_impl_8_MAX) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0) ->
    (((a'₁ = 4294967295) = True)) ∧
    (((¬((4294967295 + 1) ≤ num_impl_8_MAX)) = True)) ∧
    (∀ (a'₂ : Int),
     (a'₂ = (5 - 3)) ->
      ((k1 a'₂ a'₁))) ∧
    (∀ (a'₃ : Int),
     ((k1 a'₃ a'₁)) ->
      (a'₃ ≥ 0) ->
       ((a'₃ = 2) = True))
    )
 
end F
