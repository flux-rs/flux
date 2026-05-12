import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestIter := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (∀ (v₀ : Int),
  (0 ≤ v₀) ->
   ((k1 v₀))) ∧
 (∀ (a'₂ : Int),
  (a'₂ = 0) ->
   (k0 a'₂) ->
    (∀ (a'₃ : Int),
     ((k1 a'₃)) ->
      ((k2 a'₃))) ∧
    (∀ (a'₄ : Int),
     ((k2 a'₄)) ->
      (((0 ≤ a'₄) = True)) ∧
      (∀ (a'₅ : Int),
       ((k2 a'₅)) ->
        ((k1 a'₅)))
      )
    )
 
end F
