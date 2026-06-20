import Structs.EnumJoin.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (∀ (a'₁ : Prop),
  ∀ (a'₂ : Int),
   (a'₂ = 0) ->
    (k0 a'₂)) ∧
 (∀ (a'₃ : Int),
  (a'₃ = 0) ->
   (k0 a'₃) ->
    (∀ (v₀ : Int),
     (v₀ ≥ 0) ->
      ((k1 v₀))) ∧
    (((k1 0))) ∧
    (∀ (a'₅ : Int),
     ((k1 a'₅)) ->
      (a'₅ ≥ 0))
    )
 
end F
