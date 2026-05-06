import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def GetNth := 
 ∀ (n₀ : Int),
  ∀ (k₀ : Int),
   (k₀ < n₀) ->
    (n₀ ≥ 0) ->
     (k₀ ≥ 0) ->
      ((n₀ = 0) ->
       False) ∧
      (∀ (n₁ : Int),
       (n₀ = (n₁ + 1)) ->
        ∀ (a'₁ : Int),
         (n₁ ≥ 0) ->
          (k₀ ≠ 0) ->
           (((k₀ - 1) ≥ 0)) ∧
           (((k₀ - 1) < n₁))
           )
      
end F
