import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
import LeanFixpoint
open Classical

namespace F



def Goofy := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ = 99) ->
   (((k0 0 n₀))) ∧
   (((k0 n₀ n₀))) ∧
   (((k0 0 n₀)) ->
    ((k0 n₀ n₀)) ->
     (((n₀ = n₀) = True)) ∧
     (((k1 0 n₀ n₀))) ∧
     (∀ (thing₀ : Int),
      ∀ (thing₁ : Int),
       ((k1 thing₀ thing₁ n₀)) ->
        ∀ (r₀ : (OpsRangeRange Int)),
         (((thing₀ < thing₁) -> ((OpsRangeRange.start r₀) = (thing₀ + 1))) ∧ ((OpsRangeRange.end_ r₀) = thing₁)) ->
          ((thing₀ < thing₁) = True) ->
           ∀ (a'₃ : Int),
            (a'₃ = thing₀) ->
             (((0 ≤ a'₃) = True)) ∧
             (((a'₃ < n₀) = True)) ∧
             (((k1 (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) n₀)))
             )
     )
   
end F
