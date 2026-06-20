import Structs.EnumJoin.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   ((k0 a'₀))) ∧
 (∀ (a'₁ : Prop),
  ∀ (a'₂ : Int),
   (a'₂ ≥ 0) ->
    ((k0 a'₂))) ∧
 (∀ (y₀ : Int),
  ((k0 y₀)) ->
   ((y₀ + 1) > 0))
 
end F
