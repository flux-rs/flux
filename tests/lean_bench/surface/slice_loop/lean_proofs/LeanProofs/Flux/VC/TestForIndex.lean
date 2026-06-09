import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def TestForIndex := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (((k0 0 a'₀ a'₀))) ∧
   (∀ (iter₀ : (OpsRangeRange Int)),
    ((k0 (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) a'₀)) ->
     ∀ (r₀ : (OpsRangeRange Int)),
      ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
       (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
        ∀ (a'₃ : Int),
         (a'₃ = (OpsRangeRange.start iter₀)) ->
          (a'₃ ≥ 0) ->
           ((a'₃ < a'₀)) ∧
           ((a'₃ < a'₀) ->
            ∀ (v₀ : Int),
             (v₀ > 666) ->
              ((k0 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₀)))
           )
   
end F
