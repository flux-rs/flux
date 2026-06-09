import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def KnuthShuffle := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (n₀ ≥ 0) ->
    (((k0 0 n₀))) ∧
    (∀ (n₁ : Int),
     ((k0 n₁ n₀)) ->
      (n₁ < n₀) ->
       (((n₀ - n₁) ≥ 0)) ∧
       ((0 < (n₀ - n₁))) ∧
       (∀ (i₀ : Int),
        ((0 ≤ i₀) ∧ (i₀ < (n₀ - n₁))) ->
         (i₀ ≥ 0) ->
          (((n₀ - n₁) ≥ 0)) ∧
          ((((n₀ - n₁) - 1) ≥ 0)) ∧
          ((i₀ < n₀)) ∧
          ((((n₀ - n₁) - 1) < n₀)) ∧
          (((k0 (n₁ + 1) n₀)))
          )
       )
    
end F
