import Lifetimes.ListMutRef.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__0__GetMut := 
 ∀ (n₀ : Int),
  ∀ (idx₀ : Int),
   (idx₀ < n₀) ->
    (n₀ ≥ 0) ->
     (idx₀ ≥ 0) ->
      ((n₀ = 0) ->
       False) ∧
      (∀ (n₁ : Int),
       (n₀ = (n₁ + 1)) ->
        (n₁ ≥ 0) ->
         (idx₀ ≠ 0) ->
          (((idx₀ - 1) ≥ 0)) ∧
          (((idx₀ - 1) < n₁))
          )
      
end F
