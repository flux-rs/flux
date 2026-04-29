import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.IterAdaptersEnumerateEnumerate
import LeanProofs.Flux.Struct.SliceIterIter
import LeanFixpoint
open Classical

namespace F



def TestEnumer4 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 0 0 n₀ n₀))) ∧
   (∀ (iter₀ : (IterAdaptersEnumerateEnumerate SliceIterIter)),
    ((k0 (IterAdaptersEnumerateEnumerate.idx iter₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner iter₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner iter₀)) n₀)) ->
     ∀ (next_s₀ : (IterAdaptersEnumerateEnumerate SliceIterIter)),
      ((((IterAdaptersEnumerateEnumerate.idx iter₀) + 1) = (IterAdaptersEnumerateEnumerate.idx next_s₀)) ∧ (((SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner iter₀)) + 1) = (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀))) ∧ ((SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner iter₀)) = (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)))) ->
       ((¬((SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner iter₀)) ≥ (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner iter₀)))) = True) ->
        ∀ (a'₂ : Int),
         ((IterAdaptersEnumerateEnumerate.idx iter₀) ≥ 0) ->
          (a'₂ ≥ 0) ->
           ((((IterAdaptersEnumerateEnumerate.idx iter₀) < n₀) = True)) ∧
           (((k0 (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)) n₀)))
           )
   
end F
