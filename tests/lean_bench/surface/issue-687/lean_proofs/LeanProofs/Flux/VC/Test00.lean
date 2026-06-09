import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test00 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (check₀ : Int),
  (check₀ ≥ 0) ->
   ∀ (a'₀ : Int),
    ((check₀ = a'₀) -> (a'₀ > 0)) ->
     (a'₀ ≥ 0) ->
      (¬(a'₀ ≠ check₀)) ->
       (((k0 a'₀ check₀ a'₀))) ∧
       (∀ (a'₁ : Int),
        ((k0 a'₁ check₀ a'₀)) ->
         (a'₁ > 0))
       
end F
