import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def IsFebDay := ∃ k0 : (a0 : Prop) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (d₀ : Int),
  ∀ (y₀ : Int),
   (d₀ ≥ 0) ->
    (y₀ ≥ 0) ->
     ((¬(d₀ ≤ 29)) ->
      (False = ((d₀ ≤ 29) ∧ ((d₀ = 29) -> (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0))))))) ∧
     ((d₀ ≤ 29) ->
      ((¬(d₀ ≠ 29)) ->
       ((k0 (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0))) d₀ y₀))) ∧
      ((d₀ ≠ 29) ->
       ((k0 True d₀ y₀))) ∧
      (∀ (a'₀ : Prop),
       ((k0 a'₀ d₀ y₀)) ->
        (a'₀ = ((d₀ = 29) -> (((y₀ % 400) = 0) ∨ (((y₀ % 4) = 0) ∧ ((y₀ % 100) > 0))))))
      )
     
end F
