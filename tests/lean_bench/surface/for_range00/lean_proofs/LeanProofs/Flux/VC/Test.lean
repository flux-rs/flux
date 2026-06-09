import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Prop) -> Prop, 
 ∀ (len₀ : Int),
  (len₀ ≥ 0) ->
   (((k0 0 0 len₀ len₀))) ∧
   (∀ (del₀ : Int),
    ∀ (iter₀ : (OpsRangeRange Int)),
     ((k0 del₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) len₀)) ->
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
             ((k1 del₀ len₀ del₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄ a'₅))) ∧
            (a'₅ ->
             ((k1 (del₀ + 1) len₀ del₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄ True))) ∧
            (∀ (del₁ : Int),
             ((k1 del₁ len₀ del₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₄ a'₅)) ->
              ((k0 del₁ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) len₀)))
            )
           )
        )
   
end F
