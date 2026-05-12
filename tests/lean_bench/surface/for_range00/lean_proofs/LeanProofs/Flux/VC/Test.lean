import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
import LeanFixpoint
open Classical

namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Prop) -> Prop, 
 ∀ (len₀ : Int),
  (len₀ ≥ 0) ->
   (((k0 0 len₀ 0 len₀))) ∧
   (∀ (iter₀ : (OpsRangeRange Int)),
    ∀ (del₀ : Int),
     ((k0 (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) del₀ len₀)) ->
      ∀ (r₀ : (OpsRangeRange Int)),
       ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
        ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = False) ->
         ((del₀ ≤ len₀) = True)) ∧
        ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
         ∀ (a'₄ : Int),
          (a'₄ = (OpsRangeRange.start iter₀)) ->
           (((del₀ ≤ a'₄) = True)) ∧
           (∀ (a'₅ : Prop),
            ((¬a'₅) ->
             ((k1 del₀ len₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) del₀ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄ a'₅))) ∧
            (a'₅ ->
             ((k1 (del₀ + 1) len₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) del₀ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄ True))) ∧
            (∀ (del₁ : Int),
             ((k1 del₁ len₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) del₀ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄ a'₅)) ->
              ((k0 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) del₁ len₀)))
            )
           )
        )
   
end F
