import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAddEx := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (base₀ : Int),
  ∀ (addr₀ : Int),
   ∀ (size₀ : Int),
    ((addr₀ ≥ base₀) ∧ (size₀ > 1)) ->
     (∀ (a'₀ : Int),
      ((k0 a'₀ base₀ addr₀ size₀))) ∧
     ((((addr₀ + 0) ≥ base₀)) ∧
     (((size₀ - 0) > 0))
     ) ∧
     (∀ (a'₁ : Int),
      ((k0 a'₁ base₀ addr₀ size₀)) ->
       ((k1 a'₁ base₀ addr₀ size₀))) ∧
     (∀ (_val0₀ : Int),
      ((k1 _val0₀ base₀ addr₀ size₀)) ->
       (((addr₀ + 1) ≥ base₀)) ∧
       (((size₀ - 1) > 0))
       )
     
end F
