import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def FftTest := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Prop) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Prop) -> (a8 : Int) -> (a9 : Prop) -> Prop, 
 ∀ (v₀ : Int),
  (v₀ ≥ 2) ->
   (v₀ ≥ 0) ->
    ((((v₀ / 2) - 1) ≥ 0)) ∧
    ((0 ≤ (v₀ + 1)) ->
     ((1 < (v₀ + 1))) ∧
     ((1 < (v₀ + 1))) ∧
     ((((v₀ / 2) + 1) < (v₀ + 1))) ∧
     ((((v₀ / 2) + 1) < (v₀ + 1))) ∧
     (((k0 1 v₀))) ∧
     (∀ (i₀ : Int),
      ((k0 i₀ v₀)) ->
       ((¬(i₀ ≤ ((v₀ / 2) - 1))) ->
        ((2 ≤ (v₀ + 1))) ∧
        (∀ (a'₂ : Int),
         (((k1 0 0 0 v₀ i₀ a'₂))) ∧
         (∀ (i₁ : Int),
          ∀ (_ki₀ : Int),
           ∀ (_kr₀ : Int),
            ((k1 i₁ _ki₀ _kr₀ v₀ i₀ a'₂)) ->
             (i₁ < v₀) ->
              (((i₁ + 1) < (v₀ + 1))) ∧
              (∀ (a'₆ : Prop),
               ((¬a'₆) ->
                ((k2 _kr₀ v₀ i₀ a'₂ i₁ _ki₀ _kr₀ a'₆))) ∧
               (a'₆ ->
                ((k2 i₁ v₀ i₀ a'₂ i₁ _ki₀ _kr₀ True))) ∧
               (∀ (_kr₁ : Int),
                ((k2 _kr₁ v₀ i₀ a'₂ i₁ _ki₀ _kr₀ a'₆)) ->
                 (((i₁ + 1) < (v₀ + 1))) ∧
                 (∀ (a'₈ : Prop),
                  ((¬a'₈) ->
                   ((k3 _ki₀ v₀ i₀ a'₂ i₁ _ki₀ _kr₀ a'₆ _kr₁ a'₈))) ∧
                  (a'₈ ->
                   ((k3 i₁ v₀ i₀ a'₂ i₁ _ki₀ _kr₀ a'₆ _kr₁ True))) ∧
                  (∀ (_ki₁ : Int),
                   ((k3 _ki₁ v₀ i₀ a'₂ i₁ _ki₀ _kr₀ a'₆ _kr₁ a'₈)) ->
                    ((k1 (i₁ + 1) _ki₁ _kr₁ v₀ i₀ a'₂)))
                  )
                 )
               )
              )
         )
        ) ∧
       ((i₀ ≤ ((v₀ / 2) - 1)) ->
        (((v₀ - i₀) ≥ 0)) ∧
        (((i₀ + 1) < (v₀ + 1))) ∧
        ((((v₀ - i₀) + 1) < (v₀ + 1))) ∧
        (((i₀ + 1) < (v₀ + 1))) ∧
        ((((v₀ - i₀) + 1) < (v₀ + 1))) ∧
        (((k0 (i₀ + 1) v₀)))
        )
       )
     )
    
end F
