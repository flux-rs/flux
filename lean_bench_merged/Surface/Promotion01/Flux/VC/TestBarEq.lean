import Surface.Promotion01.Flux.Prelude
import Surface.Promotion01.Flux.Struct.Gib
open Classical
set_option linter.unusedVariables false


namespace F



def TestBarEq := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Gib) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Gib) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k0 a'₀)) ∧
 (((k1 (Gib.mkGib₁)))) ∧
 (∀ (a'₁ : Int),
  (a'₁ = 0) ->
   (k2 a'₁)) ∧
 (((k3 (Gib.mkGib₁)))) ∧
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
