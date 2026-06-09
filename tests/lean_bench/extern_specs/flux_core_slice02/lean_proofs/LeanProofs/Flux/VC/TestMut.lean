import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestMut := 
 ∀ (constgen_N_0 : Int),
  (constgen_N_0 ≥ 4) ->
   (constgen_N_0 ≥ 0) ->
    ((4 ≤ constgen_N_0)) ∧
    (∀ (out₀ : Int),
     (out₀ = (4 - 2)) ->
      (out₀ ≥ 0) ->
       (((out₀ = 2) = True)) ∧
       ((0 < out₀)) ∧
       ((0 < out₀) ->
        ((1 < out₀)) ∧
        ((1 < out₀) ->
         ((3 ≤ constgen_N_0)) ∧
         (∀ (out₁ : Int),
          (out₁ = 3) ->
           (out₁ ≥ 0) ->
            ((0 < out₁)) ∧
            ((0 < out₁) ->
             ((2 < out₁)) ∧
             ((2 < out₁) ->
              ((2 ≤ constgen_N_0)) ∧
              (∀ (out₂ : Int),
               (out₂ = (constgen_N_0 - 2)) ->
                (out₂ ≥ 0) ->
                 (((constgen_N_0 - 2) ≥ 0)) ∧
                 ((0 < out₂)) ∧
                 ((0 < out₂) ->
                  (1 < out₂))
                 )
              )
             )
            )
         )
        )
       )
    
end F
