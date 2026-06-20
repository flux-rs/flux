import Enums.List00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Mappend := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n1₀ : Int),
  ∀ (n2₀ : Int),
   (n1₀ ≥ 0) ->
    (n2₀ ≥ 0) ->
     ((n1₀ = 0) ->
      ((k0 n2₀ n1₀ n2₀))) ∧
     (∀ (n₀ : Int),
      (n1₀ = (n₀ + 1)) ->
       ∀ (a'₁ : Int),
        (n₀ ≥ 0) ->
         ((n₀ + n2₀) ≥ 0) ->
          ((k0 ((n₀ + n2₀) + 1) n1₀ n2₀))) ∧
     (∀ (a'₂ : Int),
      ((k0 a'₂ n1₀ n2₀)) ->
       (a'₂ = (n1₀ + n2₀)))
     
end F
