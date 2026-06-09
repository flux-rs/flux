import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl8MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestUpperBoundedUConcrete := ∃ k0 : (a0 : Int) -> Prop, 
 (((1000 ≤ num_impl_8_MAX) = True)) ∧
 (∀ (a'₀ : Int),
  (a'₀ = 1000) ->
   ((k0 a'₀))) ∧
 (((1000 ≤ num_impl_8_MAX) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0) ->
    (((a'₁ = 1000) = True)) ∧
    (((¬((4294967295 + 1) ≤ num_impl_8_MAX)) = True))
    )
 
end F
