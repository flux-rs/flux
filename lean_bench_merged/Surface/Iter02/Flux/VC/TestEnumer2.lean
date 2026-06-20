import Surface.Iter02.Flux.Prelude
import Surface.Iter02.Flux.Struct.IterAdaptersEnumerateEnumerate
import Surface.Iter02.Flux.Struct.SliceIterIter
open Classical
set_option linter.unusedVariables false


namespace F



def TestEnumer2 := 
 ∀ (next_s₀ : (IterAdaptersEnumerateEnumerate SliceIterIter)),
  (((0 + 1) = (IterAdaptersEnumerateEnumerate.idx next_s₀)) ∧ ((0 + 1) = (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀))) ∧ (1 = (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)))) ->
   ∀ (next_s₁ : (IterAdaptersEnumerateEnumerate SliceIterIter)),
    ((((IterAdaptersEnumerateEnumerate.idx next_s₀) + 1) = (IterAdaptersEnumerateEnumerate.idx next_s₁)) ∧ (((SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) + 1) = (SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₁))) ∧ ((SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀)) = (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₁)))) ->
     (((SliceIterIter.idx (IterAdaptersEnumerateEnumerate.inner next_s₀)) ≥ (SliceIterIter.len (IterAdaptersEnumerateEnumerate.inner next_s₀))) = True)
end F
