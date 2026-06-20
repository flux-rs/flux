import Surface.ForRange00.Flux.Prelude
import Surface.ForRange00.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def Mickey := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ = 99) ->
   (((k0 0 n₀ n₀))) ∧
   (∀ (iter₀ : (OpsRangeRange Int)),
    ((k0 (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) n₀)) ->
     ∀ (r₀ : (OpsRangeRange Int)),
      ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
       (((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
        ∀ (a'₂ : Int),
         (a'₂ = (OpsRangeRange.start iter₀)) ->
          (((0 ≤ a'₂) = True)) ∧
          (((a'₂ < n₀) = True)) ∧
          (((k0 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) n₀)))
          )
   
end F
