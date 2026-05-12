import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.AllocLayoutLayout
import LeanProofs.Flux.Fun.NumImpl5MAX
import LeanFixpoint
open Classical

namespace F



def TestArrayUnwrap := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 (∀ (a'₀ : AllocLayoutLayout),
  (a'₀ = (AllocLayoutLayout.mkAllocLayoutLayout₀ (10 * 4) 4)) ->
   ((k0 (AllocLayoutLayout.size a'₀) (AllocLayoutLayout.align a'₀)))) ∧
 (((False ∨ ((((4 * 10) + 4) - 1) ≤ num_impl_5_MAX)) = True)) ∧
 (∀ (x₀ : AllocLayoutLayout),
  ((k0 (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀))) ->
   (((AllocLayoutLayout.align x₀) > 0) ∧ ((BitVec.and (BitVec.ofInt 64 (AllocLayoutLayout.align x₀)) (BitVec.sub (BitVec.ofInt 64 (AllocLayoutLayout.align x₀)) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) ->
    ((((AllocLayoutLayout.size x₀) + (AllocLayoutLayout.align x₀)) - 1) ≤ num_impl_5_MAX) ->
     (∀ (a'₂ : AllocLayoutLayout),
      (a'₂ = (AllocLayoutLayout.mkAllocLayoutLayout₀ (5 * 4) 4)) ->
       ((k1 (AllocLayoutLayout.size a'₂) (AllocLayoutLayout.align a'₂) (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀)))) ∧
     (((False ∨ ((((4 * 5) + 4) - 1) ≤ num_impl_5_MAX)) = True)) ∧
     (∀ (y₀ : AllocLayoutLayout),
      ((k1 (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀) (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀))) ->
       (((AllocLayoutLayout.align y₀) > 0) ∧ ((BitVec.and (BitVec.ofInt 64 (AllocLayoutLayout.align y₀)) (BitVec.sub (BitVec.ofInt 64 (AllocLayoutLayout.align y₀)) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) ->
        ((((AllocLayoutLayout.size y₀) + (AllocLayoutLayout.align y₀)) - 1) ≤ num_impl_5_MAX) ->
         (∀ (a'₄ : AllocLayoutLayout),
          (a'₄ = (AllocLayoutLayout.mkAllocLayoutLayout₀ (20 * 0) 1)) ->
           ((k2 (AllocLayoutLayout.size a'₄) (AllocLayoutLayout.align a'₄) (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀) (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀)))) ∧
         (((True ∨ ((((0 * 20) + 1) - 1) ≤ num_impl_5_MAX)) = True)) ∧
         (∀ (z₀ : AllocLayoutLayout),
          ((k2 (AllocLayoutLayout.size z₀) (AllocLayoutLayout.align z₀) (AllocLayoutLayout.size x₀) (AllocLayoutLayout.align x₀) (AllocLayoutLayout.size y₀) (AllocLayoutLayout.align y₀))) ->
           (((AllocLayoutLayout.align z₀) > 0) ∧ ((BitVec.and (BitVec.ofInt 64 (AllocLayoutLayout.align z₀)) (BitVec.sub (BitVec.ofInt 64 (AllocLayoutLayout.align z₀)) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) ->
            ((((AllocLayoutLayout.size z₀) + (AllocLayoutLayout.align z₀)) - 1) ≤ num_impl_5_MAX) ->
             ((AllocLayoutLayout.size x₀) ≥ 0) ->
              ((((AllocLayoutLayout.size x₀) = (4 * 10)) = True)) ∧
              (((AllocLayoutLayout.align x₀) ≥ 0) ->
               ((((AllocLayoutLayout.align x₀) = 4) = True)) ∧
               (((AllocLayoutLayout.size y₀) ≥ 0) ->
                ((((AllocLayoutLayout.size y₀) = (4 * 5)) = True)) ∧
                (((AllocLayoutLayout.align y₀) ≥ 0) ->
                 ((((AllocLayoutLayout.align y₀) = 4) = True)) ∧
                 (((AllocLayoutLayout.size z₀) ≥ 0) ->
                  ((((AllocLayoutLayout.size z₀) = 0) = True)) ∧
                  (((AllocLayoutLayout.align z₀) ≥ 0) ->
                   (((AllocLayoutLayout.align z₀) = 1) = True))
                  )
                 )
                )
               )
              )
         )
     )
 
end F
