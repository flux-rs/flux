import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestNext := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k0 a'₁) ->
    ∀ (a'₂ : Int),
     ((10 ≤ a'₂) ∧ (a'₂ < 15)) ->
      (((k1 True a'₂))) ∧
      (∀ (a'₃ : Prop),
       ((k1 a'₃ a'₂)) ->
        (a'₃ = True))
      )
 
end F
