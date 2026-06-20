import Detached.DetachImpl01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__2__From := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   ((n₀ = 0) ->
    ((k0 0 n₀))) ∧
   (∀ (n₁ : Int),
    (n₀ = (n₁ + 1)) ->
     (0 ≤ n₁) ->
      (n₁ ≥ 0) ->
       ((k0 (1 + n₁) n₀))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁ n₀)) ->
     (a'₁ = n₀))
   
end F
