import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def InitRatioC := 
 ∀ (m₀ : Int),
  ∀ (n₀ : Int),
   ∀ (j₀ : Int),
    ∀ (i₀ : Int),
     (0 < m₀) ->
      (0 < n₀) ->
       ((0 < j₀) ∧ (j₀ < n₀)) ->
        ((0 < i₀) ∧ (i₀ < m₀)) ->
         (m₀ ≥ 0) ->
          (n₀ ≥ 0) ->
           (j₀ ≥ 0) ->
            (i₀ ≥ 0) ->
             (((n₀ - 1) ≥ 0)) ∧
             (((n₀ - 1) < n₀))
             
end F
