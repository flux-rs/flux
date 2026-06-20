import Surface.Closure11.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Dot := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (∀ (a'₀ : Int),
    ((k0 a'₀ n₀)) ->
     (a'₀ ≥ 0) ->
      ((a'₀ < n₀)) ∧
      (∀ (a'₁ : Int),
       ((k1 a'₁ n₀ a'₀))) ∧
      (∀ (a'₂ : Int),
       ((k1 a'₂ n₀ a'₀)) ->
        (a'₀ < n₀))
      ) ∧
   (∀ (v₀ : Int),
    (v₀ < n₀) ->
     ((k0 v₀ n₀)))
   
end F
