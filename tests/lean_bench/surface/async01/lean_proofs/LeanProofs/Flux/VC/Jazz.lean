import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Jazz := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, 
 ∀ (k₀ : Int),
  (0 ≤ k₀) ->
   ∀ (a'₀ : Int),
    ∀ (a'₁ : Int),
     (((k0 a'₁ k₀ a'₀ a'₁))) ∧
     (∀ (a'₂ : Int),
      ((k0 a'₂ k₀ a'₀ a'₁)) ->
       ∀ (a'₃ : Int),
        (∀ (a'₄ : Int),
         (k₀ ≤ a'₄) ->
          ((0 ≤ a'₄)) ∧
          (∀ (a'₅ : Int),
           ∀ (a'₆ : Int),
            (((k1 a'₆ k₀ a'₀ a'₁ a'₂ a'₃ a'₄ a'₅ a'₆))) ∧
            (∀ (a'₇ : Int),
             ((k1 a'₇ k₀ a'₀ a'₁ a'₂ a'₃ a'₄ a'₅ a'₆)) ->
              ∀ (a'₈ : Int),
               (∀ (a'₉ : Int),
                (a'₄ ≤ a'₉) ->
                 (k₀ ≤ a'₉)) ∧
               (((k1 a'₈ k₀ a'₀ a'₁ a'₂ a'₃ a'₄ a'₅ a'₆)))
               )
            )
          ) ∧
        (((k0 a'₃ k₀ a'₀ a'₁)))
        )
     
end F
