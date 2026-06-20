import Surface.OutputExists01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (n₀ ≥ 0) ->
    (¬(n₀ ≠ 10)) ->
     ((n₀ > 0)) ∧
     (∀ (a'₀ : Int),
      ((k0 a'₀ n₀))) ∧
     ((0 ≤ (n₀ - 1)) ->
      ∀ (a'₁ : Int),
       ((k0 a'₁ n₀)) ->
        (n₀ > 0))
     
end F
