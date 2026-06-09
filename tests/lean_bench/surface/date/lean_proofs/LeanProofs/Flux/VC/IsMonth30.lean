import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def IsMonth30 := ∃ k0 : (a0 : Int) -> Prop, 
 ∀ (m₀ : Int),
  (m₀ ≥ 0) ->
   ((m₀ ≠ 4) ->
    ((m₀ ≠ 6) ->
     ((m₀ ≠ 9) ->
      ((m₀ = 11) = ((((m₀ = 4) ∨ (m₀ = 6)) ∨ (m₀ = 9)) ∨ (m₀ = 11)))) ∧
     ((¬(m₀ ≠ 9)) ->
      ((k0 m₀)))
     ) ∧
    ((¬(m₀ ≠ 6)) ->
     ((k0 m₀)))
    ) ∧
   ((¬(m₀ ≠ 4)) ->
    ((k0 m₀))) ∧
   (((k0 m₀)) ->
    (True = ((((m₀ = 4) ∨ (m₀ = 6)) ∨ (m₀ = 9)) ∨ (m₀ = 11))))
   
end F
