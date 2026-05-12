import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.OpsRangeRange
import LeanFixpoint
open Classical

namespace F



def FillVecLoop := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (n₀ : Int),
   ∀ (f₀ : Int),
    (n₀ ≥ 0) ->
     (((k0 0 f₀ 0 n₀ n₀ f₀))) ∧
     (∀ (res₀ : Int),
      ∀ (f₁ : Int),
       ∀ (iter₀ : (OpsRangeRange Int)),
        ((k0 res₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) n₀ f₀)) ->
         ∀ (r₀ : (OpsRangeRange Int)),
          ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
           ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = False) ->
            (res₀ = n₀)) ∧
           ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
            ∀ (a'₅ : Int),
             (a'₅ = (OpsRangeRange.start iter₀)) ->
              (a'₅ ≥ 0) ->
               (∀ (a'₆ : Int),
                ((k1 a'₆ n₀ f₀ res₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 ∀ (a'₇ : Int),
                  ((k1 a'₇ n₀ f₀ res₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                   ∀ (a'₈ : Int),
                    ((k2 a'₈ n₀ f₀ res₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
               (False ->
                (c0)) ∧
               (((k1 f₁ n₀ f₀ res₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅))) ∧
               (∀ (a'₉ : Int),
                ((k2 a'₉ n₀ f₀ res₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                 ∀ (a'₁₀ : Int),
                  ((k1 a'₁₀ n₀ f₀ res₀ f₁ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₅)) ->
                   (0 ≤ (res₀ + 1)) ->
                    ((k0 (res₀ + 1) a'₁₀ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) n₀ f₀)))
               )
           )
     
end F
