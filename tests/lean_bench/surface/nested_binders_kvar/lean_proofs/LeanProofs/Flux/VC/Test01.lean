import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (((k0 n₀ n₀))) ∧
  (∀ (a'₁ : Int),
   (a'₁ = n₀) ->
    ((k1 a'₁ n₀ n₀))) ∧
  (∀ (x₀ : Int),
   ((k0 x₀ n₀)) ->
    ∀ (a'₃ : Int),
     ((k1 a'₃ x₀ n₀)) ->
      (a'₃ = x₀))
  
end F
