import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestAddEx := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (v₀ : Int),
  ((c0 v₀) > 1) ->
   (∀ (a'₁ : Int),
    ((k0 a'₁ v₀))) ∧
   (∀ (p₀ : Int),
    ((c0 p₀) = ((c0 v₀) - 0)) ->
     (((c0 p₀) > 0)) ∧
     (∀ (a'₃ : Int),
      ((k0 a'₃ v₀)) ->
       ((k1 a'₃ v₀ p₀))) ∧
     (∀ (_val0₀ : Int),
      ((k1 _val0₀ v₀ p₀)) ->
       ∀ (p₁ : Int),
        ((c0 p₁) = ((c0 v₀) - 1)) ->
         ((c0 p₁) > 0))
     )
   
end F
