import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.IterAdaptersEnumerateEnumerate
import LeanProofs.Flux.Struct.SliceIterIter
import LeanFixpoint
open Classical

namespace F



def TestEnumerate1 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ > 1) ->
   (n₀ ≥ 0) ->
    (((n₀ > 0) = True)) ∧
    (∀ (next_s₀ : (IterAdaptersEnumerateEnumerate SliceIterIter)),
     (((0 + 1) = (IterAdaptersEnumerateEnumerate.idx next_s₀)) ∧ ((0 + 1) = (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀))) ∧ (n₀ = (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)))) ->
      (((¬(0 ≥ n₀)) = True)) ∧
      (∀ (a'₂ : Int),
       (((k0 0 n₀ (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀))))) ∧
       (((k1 a'₂ n₀ (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)))))
       ) ∧
      (((¬(0 ≥ n₀)) = True)) ∧
      (∀ (a'₃ : Int),
       ((k0 a'₃ n₀ (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)))) ->
        ∀ (a'₄ : Int),
         ((k1 a'₄ n₀ (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)))) ->
          (a'₃ ≥ 0) ->
           (a'₄ ≥ 0) ->
            (((a'₃ = 0) = True)) ∧
            (∀ (next_s₁ : (IterAdaptersEnumerateEnumerate SliceIterIter)),
             ((((IterAdaptersEnumerateEnumerate.idx next_s₀) + 1) = (IterAdaptersEnumerateEnumerate.idx next_s₁)) ∧ (((SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) + 1) = (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₁))) ∧ ((SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)) = (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₁)))) ->
              (((¬((SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) ≥ (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)))) = True)) ∧
              (∀ (a'₆ : Int),
               (((k2 (IterAdaptersEnumerateEnumerate.idx next_s₀) n₀ (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)) a'₃ a'₄ (IterAdaptersEnumerateEnumerate.idx next_s₁) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₁)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₁))))) ∧
               (((k3 a'₆ n₀ (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)) a'₃ a'₄ (IterAdaptersEnumerateEnumerate.idx next_s₁) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₁)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₁)))))
               ) ∧
              (((¬((SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) ≥ (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)))) = True)) ∧
              (∀ (a'₇ : Int),
               ((k2 a'₇ n₀ (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)) a'₃ a'₄ (IterAdaptersEnumerateEnumerate.idx next_s₁) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₁)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₁)))) ->
                ∀ (a'₈ : Int),
                 ((k3 a'₈ n₀ (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)) a'₃ a'₄ (IterAdaptersEnumerateEnumerate.idx next_s₁) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₁)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₁)))) ->
                  (a'₇ ≥ 0) ->
                   (a'₈ ≥ 0) ->
                    ((a'₇ = 1) = True))
              )
            )
      )
    
end F
