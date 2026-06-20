import Surface.Simplex.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def IsNeg := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (m₀ : Int),
  ∀ (n₀ : Int),
   (m₀ > 0) ->
    (n₀ > 0) ->
     (m₀ ≥ 0) ->
      (n₀ ≥ 0) ->
       (((k0 1 m₀ n₀))) ∧
       (∀ (j₀ : Int),
        ((k0 j₀ m₀ n₀)) ->
         (((n₀ - 1) ≥ 0)) ∧
         ((j₀ < (n₀ - 1)) ->
          ((0 < m₀)) ∧
          ((j₀ < n₀)) ∧
          (∀ (a'₁ : Prop),
           (¬a'₁) ->
            ((k0 (j₀ + 1) m₀ n₀)))
          )
         )
       
end F
