import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Foo := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (len₀ : Int),
  (0 ≤ len₀) ->
   (len₀ ≥ 0) ->
    (((k0 0 len₀))) ∧
    (∀ (i₀ : Int),
     ((k0 i₀ len₀)) ->
      (i₀ < len₀) ->
       (((k1 len₀ i₀))) ∧
       ((0 ≤ i₀)) ∧
       (((k1 len₀ i₀)) ->
        ((k2 len₀ i₀))) ∧
       (((k2 len₀ i₀)) ->
        ((k1 len₀ i₀))) ∧
       (((k3 (i₀ + 1) len₀ i₀))) ∧
       (((k2 len₀ i₀)) ->
        ((k4 (i₀ + 1) len₀ i₀))) ∧
       (((k4 (i₀ + 1) len₀ i₀)) ->
        ((k2 len₀ i₀))) ∧
       (∀ (i₁ : Int),
        (((0 ≤ i₁) ∧ (i₁ < len₀) ∧ (i₁ ≠ i₀)) ->
         ((k5 i₁ (i₀ + 1) len₀ i₀))) ∧
        (((k5 i₁ (i₀ + 1) len₀ i₀)) ->
         ((0 ≤ i₁)) ∧
         ((i₁ < len₀)) ∧
         ((i₁ ≠ i₀))
         )
        ) ∧
       (((k2 len₀ i₀)) ->
        ((k6 (i₀ + 1) len₀ i₀))) ∧
       (((k6 (i₀ + 1) len₀ i₀)) ->
        ((k2 len₀ i₀))) ∧
       (∀ (j₀ : Int),
        ((k3 j₀ len₀ i₀)) ->
         ((¬(j₀ < len₀)) ->
          ((k0 (i₀ + 1) len₀))) ∧
         ((j₀ < len₀) ->
          (((k5 j₀ j₀ len₀ i₀))) ∧
          (((k4 j₀ len₀ i₀)) ->
           ((k7 len₀ i₀ j₀))) ∧
          (((k7 len₀ i₀ j₀)) ->
           ((k4 j₀ len₀ i₀))) ∧
          (((k6 j₀ len₀ i₀)) ->
           ((k7 len₀ i₀ j₀)) ->
            (((k3 (j₀ + 1) len₀ i₀))) ∧
            (((k4 (j₀ + 1) len₀ i₀))) ∧
            (∀ (i₂ : Int),
             ((((k5 i₂ j₀ len₀ i₀)) ∧ (i₂ ≠ j₀)) ->
              ((k5 i₂ (j₀ + 1) len₀ i₀))) ∧
             (((k5 i₂ (j₀ + 1) len₀ i₀)) ->
              (((k5 i₂ j₀ len₀ i₀))) ∧
              ((i₂ ≠ j₀))
              )
             ) ∧
            (((k6 (j₀ + 1) len₀ i₀)))
            )
          )
         )
       )
    
end F
