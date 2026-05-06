import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#8}BITS
import LeanFixpoint
open Classical

namespace F



def TestCountU32 := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ∀ (v₀ : Int),
    (v₀ ≤ num_{impl#8}_BITS) ->
     (v₀ ≥ 0) ->
      (((v₀ ≤ 32) = True)) ∧
      (∀ (v₁ : Int),
       (v₁ ≤ num_{impl#8}_BITS) ->
        (v₁ ≥ 0) ->
         (((v₁ ≤ 32) = True)) ∧
         (∀ (v₂ : Int),
          (v₂ ≤ num_{impl#8}_BITS) ->
           (v₂ ≥ 0) ->
            (((v₂ ≤ 32) = True)) ∧
            (∀ (v₃ : Int),
             (v₃ ≤ num_{impl#8}_BITS) ->
              (v₃ ≥ 0) ->
               (((v₃ ≤ 32) = True)) ∧
               (∀ (v₄ : Int),
                (v₄ ≤ num_{impl#8}_BITS) ->
                 (v₄ ≥ 0) ->
                  (((v₄ ≤ 32) = True)) ∧
                  (∀ (v₅ : Int),
                   (v₅ ≤ num_{impl#8}_BITS) ->
                    (v₅ ≥ 0) ->
                     ((v₅ ≤ 32) = True))
                  )
               )
            )
         )
      
end F
