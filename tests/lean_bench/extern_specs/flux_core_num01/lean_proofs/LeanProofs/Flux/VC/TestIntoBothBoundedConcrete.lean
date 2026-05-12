import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl2MIN
import LeanProofs.Flux.Fun.NumImpl2MAX
import LeanFixpoint
open Classical

namespace F



def TestIntoBothBoundedConcrete := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Prop) -> Prop, 
 ∀ (r₀ : Prop),
  (r₀ = ((num_impl_2_MIN ≤ 42) ∧ (42 ≤ num_impl_2_MAX))) ->
   ((r₀ = True)) ∧
   (∀ (v₀ : Int),
    (42 = v₀) ->
     ((k0 v₀ r₀))) ∧
   ((r₀ = True)) ∧
   (∀ (a'₂ : Int),
    ((k0 a'₂ r₀)) ->
     (((a'₂ = 42) = True)) ∧
     (∀ (r₁ : Prop),
      (r₁ = ((num_impl_2_MIN ≤ (-42)) ∧ ((-42) ≤ num_impl_2_MAX))) ->
       (∀ (v₁ : Int),
        ((-42) = v₁) ->
         ((k1 v₁ r₀ a'₂ r₁))) ∧
       ((r₁ = True)) ∧
       (∀ (a'₅ : Int),
        ((k1 a'₅ r₀ a'₂ r₁)) ->
         (((a'₅ = (-42)) = True)) ∧
         (∀ (r₂ : Prop),
          (r₂ = ((num_impl_2_MIN ≤ (2147483647 + 1)) ∧ ((2147483647 + 1) ≤ num_impl_2_MAX))) ->
           (((¬r₂) = True)) ∧
           (∀ (r₃ : Prop),
            (r₃ = ((num_impl_2_MIN ≤ ((-2147483648) - 1)) ∧ (((-2147483648) - 1) ≤ num_impl_2_MAX))) ->
             ((¬r₃) = True))
           )
         )
       )
     )
   
end F
