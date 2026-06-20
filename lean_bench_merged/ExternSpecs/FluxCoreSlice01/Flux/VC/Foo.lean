import ExternSpecs.FluxCoreSlice01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Foo := 
 ∀ (n₀ : Int),
  (n₀ ≥ 4) ->
   (n₀ ≥ 0) ->
    ((4 ≤ n₀)) ∧
    (∀ (out₀ : Int),
     (out₀ = (4 - 2)) ->
      (out₀ ≥ 0) ->
       (((out₀ = 2) = True)) ∧
       ((0 < out₀)) ∧
       ((0 < out₀) ->
        ((1 < out₀)) ∧
        ((1 < out₀) ->
         ((3 ≤ n₀)) ∧
         (∀ (out₁ : Int),
          (out₁ = 3) ->
           (out₁ ≥ 0) ->
            ((0 < out₁)) ∧
            ((0 < out₁) ->
             ((2 < out₁)) ∧
             ((2 < out₁) ->
              ((2 ≤ n₀)) ∧
              (∀ (out₂ : Int),
               (out₂ = (n₀ - 2)) ->
                (out₂ ≥ 0) ->
                 (((n₀ - 2) ≥ 0)) ∧
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
