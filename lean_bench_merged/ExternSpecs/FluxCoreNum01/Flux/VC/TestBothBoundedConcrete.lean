import ExternSpecs.FluxCoreNum01.Flux.Prelude
import ExternSpecs.FluxCoreNum01.Flux.Fun.NumImpl2MIN
import ExternSpecs.FluxCoreNum01.Flux.Fun.NumImpl2MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestBothBoundedConcrete := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ((((num_impl_2_MIN ≤ 42) ∧ (42 ≤ num_impl_2_MAX)) = True)) ∧
 (∀ (a'₀ : Int),
  (a'₀ = 42) ->
   ((k0 a'₀))) ∧
 ((((num_impl_2_MIN ≤ 42) ∧ (42 ≤ num_impl_2_MAX)) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 42) = True)) ∧
   (∀ (a'₂ : Int),
    (a'₂ = (-42)) ->
     ((k1 a'₂ a'₁))) ∧
   ((((num_impl_2_MIN ≤ (-42)) ∧ ((-42) ≤ num_impl_2_MAX)) = True)) ∧
   (∀ (a'₃ : Int),
    ((k1 a'₃ a'₁)) ->
     (((a'₃ = (-42)) = True)) ∧
     (∀ (a'₄ : Int),
      (a'₄ = 2147483647) ->
       ((k2 a'₄ a'₁ a'₃))) ∧
     ((((num_impl_2_MIN ≤ 2147483647) ∧ (2147483647 ≤ num_impl_2_MAX)) = True)) ∧
     (∀ (a'₅ : Int),
      ((k2 a'₅ a'₁ a'₃)) ->
       (((a'₅ = 2147483647) = True)) ∧
       (∀ (a'₆ : Int),
        (a'₆ = (-2147483648)) ->
         ((k3 a'₆ a'₁ a'₃ a'₅))) ∧
       ((((num_impl_2_MIN ≤ (-2147483648)) ∧ ((-2147483648) ≤ num_impl_2_MAX)) = True)) ∧
       (∀ (a'₇ : Int),
        ((k3 a'₇ a'₁ a'₃ a'₅)) ->
         (((a'₇ = (-2147483648)) = True)) ∧
         (((¬((num_impl_2_MIN ≤ (2147483647 + 1)) ∧ ((2147483647 + 1) ≤ num_impl_2_MAX))) = True)) ∧
         (((¬((num_impl_2_MIN ≤ ((-2147483648) - 1)) ∧ (((-2147483648) - 1) ≤ num_impl_2_MAX))) = True))
         )
       )
     )
   )
 
end F
