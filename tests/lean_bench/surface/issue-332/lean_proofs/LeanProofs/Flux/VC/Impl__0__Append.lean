import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__0__Append := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n1₀ : Int),
  ∀ (n2₀ : Int),
   (∀ (n₀ : Int),
    (n1₀ = (n₀ + 1)) ->
     ((k0 (n₀ + 1) n1₀ n2₀))) ∧
   ((n1₀ = 0) ->
    ((k0 0 n1₀ n2₀))) ∧
   (∀ (a'₁ : Int),
    ((k0 a'₁ n1₀ n2₀)) ->
     (a'₁ = n1₀))
   
end F
