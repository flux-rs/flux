import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test001 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (n₀ : Int),
   ∀ (frog₀ : Int),
    (∀ (a'₁ : Int),
     ((k0 a'₁ n₀ frog₀)) ->
      ∀ (a'₂ : Int),
       ((k1 a'₂ n₀ frog₀)) ->
        ((n₀ ≤ a'₂)) ∧
        (∀ (a'₃ : Int),
         ((k0 a'₃ n₀ frog₀)) ->
          ∀ (a'₄ : Int),
           ((k1 a'₄ n₀ frog₀)) ->
            ((n₀ ≤ a'₄)) ∧
            (∀ (v₀ : Int),
             (n₀ ≤ v₀) ->
              ((k2 v₀ n₀ frog₀)))
            )
        ) ∧
    (False ->
     (c0)) ∧
    (((k0 frog₀ n₀ frog₀))) ∧
    (((k1 (n₀ + 1) n₀ frog₀))) ∧
    (∀ (a'₆ : Int),
     ((k2 a'₆ n₀ frog₀)) ->
      (n₀ ≤ a'₆))
    
end F
