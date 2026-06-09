import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.IterAdaptersEnumerateEnumerate
import LeanProofs.Flux.Struct.SliceIterIter
open Classical
set_option linter.unusedVariables false


namespace F



def TestEnumer3 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 0 0 n₀ n₀))) ∧
   (∀ (e₀ : (IterAdaptersEnumerateEnumerate SliceIterIter)),
    ((k0 (IterAdaptersEnumerateEnumerate.idx e₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner e₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner e₀)) n₀)) ->
     ∀ (next_s₀ : (IterAdaptersEnumerateEnumerate SliceIterIter)),
      ((((IterAdaptersEnumerateEnumerate.idx e₀) + 1) = (IterAdaptersEnumerateEnumerate.idx next_s₀)) ∧ (((SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner e₀)) + 1) = (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀))) ∧ ((SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner e₀)) = (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)))) ->
       ((¬((SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner e₀)) ≥ (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner e₀)))) = True) ->
        ∀ (a'₂ : Int),
         ((IterAdaptersEnumerateEnumerate.idx e₀) ≥ 0) ->
          (a'₂ ≥ 0) ->
           ((((IterAdaptersEnumerateEnumerate.idx e₀) < n₀) = True)) ∧
           (((k0 (IterAdaptersEnumerateEnumerate.idx next_s₀) (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)) n₀)))
           )
   
end F
