import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.GhostTokenId
import LeanFixpoint
open Classical

namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : GhostTokenId) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : GhostTokenId) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : GhostTokenId) -> (a2 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : GhostTokenId) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (token₀ : GhostTokenId),
  (((k0 42 token₀))) ∧
  (∀ (a'₁ : Int),
   ((k0 a'₁ token₀)) ->
    ((k1 a'₁ token₀))) ∧
  (∀ (a'₂ : Int),
   ((k1 a'₂ token₀)) ->
    ((k0 a'₂ token₀))) ∧
  (∀ (a'₃ : Int),
   ((k1 a'₃ token₀)) ->
    (((k1 (a'₃ + 1) token₀))) ∧
    (∀ (a'₄ : Int),
     ((k0 a'₄ token₀)) ->
      ((k2 a'₄ token₀ a'₃))) ∧
    (∀ (a'₅ : Int),
     ((k2 a'₅ token₀ a'₃)) ->
      ((k0 a'₅ token₀))) ∧
    (∀ (a'₆ : Int),
     ((k2 a'₆ token₀ a'₃)) ->
      (((k2 (a'₆ + 1) token₀ a'₃))) ∧
      (∀ (a'₇ : Int),
       ((k0 a'₇ token₀)) ->
        ((k3 a'₇ token₀ a'₃ a'₆))) ∧
      (∀ (a'₈ : Int),
       ((k3 a'₈ token₀ a'₃ a'₆)) ->
        ((k0 a'₈ token₀))) ∧
      (∀ (a'₉ : Int),
       ((k3 a'₉ token₀ a'₃ a'₆)) ->
        (a'₉ > 0))
      )
    )
  
end F
