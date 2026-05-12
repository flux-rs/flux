import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl11BITS
import LeanFixpoint
open Classical

namespace F



def TestCountUsize := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ∀ (v₀ : Int),
    (v₀ ≤ num_impl_11_BITS) ->
     (v₀ ≥ 0) ->
      (((v₀ ≤ 64) = True)) ∧
      (∀ (v₁ : Int),
       (v₁ ≤ num_impl_11_BITS) ->
        (v₁ ≥ 0) ->
         (((v₁ ≤ 64) = True)) ∧
         (∀ (v₂ : Int),
          (v₂ ≤ num_impl_11_BITS) ->
           (v₂ ≥ 0) ->
            (((v₂ ≤ 64) = True)) ∧
            (∀ (v₃ : Int),
             (v₃ ≤ num_impl_11_BITS) ->
              (v₃ ≥ 0) ->
               (((v₃ ≤ 64) = True)) ∧
               (∀ (v₄ : Int),
                (v₄ ≤ num_impl_11_BITS) ->
                 (v₄ ≥ 0) ->
                  (((v₄ ≤ 64) = True)) ∧
                  (∀ (v₅ : Int),
                   (v₅ ≤ num_impl_11_BITS) ->
                    (v₅ ≥ 0) ->
                     ((v₅ ≤ 64) = True))
                  )
               )
            )
         )
      
end F
