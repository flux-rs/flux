import Surface.IterVec00.Flux.Prelude
import Surface.IterVec00.Flux.Struct.SliceIterIter
open Classical
set_option linter.unusedVariables false


namespace F



def TestIterForLoopVec2 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (n₀ ≥ 0) ->
    (∀ (a'₀ : Int),
     ((k0 a'₀ n₀))) ∧
    (((k1 0 0 n₀ n₀))) ∧
    (∀ (a'₁ : Int),
     ((k0 a'₁ n₀)) ->
      ((k2 a'₁ 0 0 n₀ n₀))) ∧
    (∀ (res₀ : Int),
     ∀ (iter₀ : SliceIterIter),
      ((k1 res₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) n₀)) ->
       (∀ (a'₄ : Int),
        ((k2 a'₄ res₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀) n₀)) ->
         ((k3 a'₄ n₀ res₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀)))) ∧
       (∀ (next_s₀ : SliceIterIter),
        ((((SliceIterIter.idx iter₀) + 1) = (SliceIterIter.idx next_s₀)) ∧ ((SliceIterIter.len iter₀) = (SliceIterIter.len next_s₀))) ->
         ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = False) ->
          (res₀ = n₀)) ∧
         ((((SliceIterIter.idx iter₀) < (SliceIterIter.len iter₀)) = True) ->
          ∀ (a'₆ : Int),
           ((k3 a'₆ n₀ res₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀))) ->
            (a'₆ ≥ 0) ->
             (0 ≤ (res₀ + 1)) ->
              (((k1 (res₀ + 1) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) n₀))) ∧
              (∀ (a'₇ : Int),
               ((k3 a'₇ n₀ res₀ (SliceIterIter.idx iter₀) (SliceIterIter.len iter₀))) ->
                ((k2 a'₇ (res₀ + 1) (SliceIterIter.idx next_s₀) (SliceIterIter.len next_s₀) n₀)))
              )
         )
       )
    
end F
