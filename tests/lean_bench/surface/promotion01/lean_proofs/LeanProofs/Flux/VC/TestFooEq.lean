import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.Gib
import LeanFixpoint
open Classical

namespace F



def TestFooEq := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Gib) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Gib) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (((k1 (Gib.mkGib₀)))) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k2 a'₁)) ∧
 (((k3 (Gib.mkGib₀)))) ∧
 (∀ (a'₂ : Int),
  (a'₂ = 0) ->
   (k2 a'₂) ->
    ∀ (a'₃ : Gib),
     ((k3 a'₃)) ->
      ∀ (a'₄ : Int),
       (a'₄ = 0) ->
        (k0 a'₄) ->
         ∀ (a'₅ : Gib),
          ((k1 a'₅)) ->
           ((a'₃ = a'₅) = True))
 
end F
