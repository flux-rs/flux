import ExternSpecs.FluxCoreAlloc00.Flux.Prelude
import ExternSpecs.FluxCoreAlloc00.Flux.Struct.AllocLayoutLayout
import ExternSpecs.FluxCoreAlloc00.Flux.Fun.NumImpl5MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestFromValidUnwrap := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> Prop, 
 (∀ (a'₀ : AllocLayoutLayout),
  (a'₀ = (AllocLayoutLayout.mkAllocLayoutLayout₀ 4 4)) ->
   ((k0 (AllocLayoutLayout.size a'₀) (AllocLayoutLayout.align a'₀)))) ∧
 ((((((4 + 4) - 1) ≤ num_impl_5_MAX) ∧ ((BitVec.and (BitVec.ofInt 64 4) (BitVec.sub (BitVec.ofInt 64 4) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) = True)) ∧
 (∀ (x₀ : AllocLayoutLayout),
  ((k0 (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀))) ->
   (((AllocLayoutLayout.align x₀) > 0) ∧ ((BitVec.and (BitVec.ofInt 64 (AllocLayoutLayout.align x₀)) (BitVec.sub (BitVec.ofInt 64 (AllocLayoutLayout.align x₀)) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) ->
    ((((AllocLayoutLayout.size x₀) + (AllocLayoutLayout.align x₀)) - 1) ≤ num_impl_5_MAX) ->
     (∀ (a'₂ : AllocLayoutLayout),
      (a'₂ = (AllocLayoutLayout.mkAllocLayoutLayout₀ 4 4)) ->
       ((k1 (AllocLayoutLayout.size a'₂) (AllocLayoutLayout.align a'₂) (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀)))) ∧
     ((((((4 + 4) - 1) ≤ num_impl_5_MAX) ∧ ((BitVec.and (BitVec.ofInt 64 4) (BitVec.sub (BitVec.ofInt 64 4) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) = True)) ∧
     (∀ (y₀ : AllocLayoutLayout),
      ((k1 (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀) (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀))) ->
       (((AllocLayoutLayout.align y₀) > 0) ∧ ((BitVec.and (BitVec.ofInt 64 (AllocLayoutLayout.align y₀)) (BitVec.sub (BitVec.ofInt 64 (AllocLayoutLayout.align y₀)) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) ->
        ((((AllocLayoutLayout.size y₀) + (AllocLayoutLayout.align y₀)) - 1) ≤ num_impl_5_MAX) ->
         ((AllocLayoutLayout.size x₀) ≥ 0) ->
          (((AllocLayoutLayout.size x₀) ≠ 4) ->
           ((k2 False (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀) (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀)))) ∧
          ((¬((AllocLayoutLayout.size x₀) ≠ 4)) ->
           ((AllocLayoutLayout.align x₀) ≥ 0) ->
            ((k2 ((AllocLayoutLayout.align x₀) = 4) (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀) (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀)))) ∧
          (∀ (a'₄ : Prop),
           ((k2 a'₄ (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀) (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀))) ->
            ((a'₄ = True)) ∧
            (((AllocLayoutLayout.size y₀) ≥ 0) ->
             (((AllocLayoutLayout.size y₀) ≠ 4) ->
              ((k3 False (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀) (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀) a'₄))) ∧
             ((¬((AllocLayoutLayout.size y₀) ≠ 4)) ->
              ((AllocLayoutLayout.align y₀) ≥ 0) ->
               ((k3 ((AllocLayoutLayout.align y₀) = 4) (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀) (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀) a'₄))) ∧
             (∀ (a'₅ : Prop),
              ((k3 a'₅ (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀) (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀) a'₄)) ->
               (a'₅ = True))
             )
            )
          )
     )
 
end F
