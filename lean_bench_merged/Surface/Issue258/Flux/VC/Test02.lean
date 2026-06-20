import Surface.Issue258.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test02 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, ∃ k4 : (a0 : Int) -> Prop, ∃ k5 : (a0 : Int) -> Prop, 
 (((k0 1))) ∧
 (∀ (a'₀ : Int),
  (a'₀ = 0) ->
   (k1 a'₀)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   ((k2 a'₁))) ∧
 (∀ (a'₂ : Int),
  (a'₂ = 0) ->
   (k3 a'₂)) ∧
 (∀ (a'₃ : Int),
  (a'₃ = 0) ->
   (k1 a'₃) ->
    (∀ (a'₄ : Int),
     (a'₄ = 0) ->
      (k4 a'₄)) ∧
    (∀ (a'₅ : Int),
     ((k2 a'₅)) ->
      ((k5 a'₅)))
    ) ∧
 (∀ (a'₆ : Int),
  (a'₆ = 0) ->
   (k3 a'₆) ->
    ∀ (a'₇ : Int),
     (a'₇ = 0) ->
      (k4 a'₇) ->
       ∀ (a'₈ : Int),
        ((k5 a'₈)) ->
         (a'₈ > 0))
 
end F
