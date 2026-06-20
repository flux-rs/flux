import Surface.Issue258.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test03 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, ∃ k4 : (a0 : Int) -> Prop, ∃ k5 : (a0 : Int) -> Prop, ∃ k6 : (a0 : Int) -> Prop, ∃ k7 : (a0 : Int) -> Prop, ∃ k8 : (a0 : Int) -> Prop, ∃ k9 : (a0 : Int) -> Prop, 
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
   (k6 a'₆)) ∧
 (∀ (a'₇ : Int),
  (a'₇ = 0) ->
   (k3 a'₇) ->
    (∀ (a'₈ : Int),
     (a'₈ = 0) ->
      (k7 a'₈)) ∧
    (∀ (a'₉ : Int),
     (a'₉ = 0) ->
      (k4 a'₉) ->
       (∀ (a'₁₀ : Int),
        (a'₁₀ = 0) ->
         (k8 a'₁₀)) ∧
       (∀ (a'₁₁ : Int),
        ((k5 a'₁₁)) ->
         ((k9 a'₁₁)))
       )
    ) ∧
 (∀ (a'₁₂ : Int),
  (a'₁₂ = 0) ->
   (k6 a'₁₂) ->
    ∀ (a'₁₃ : Int),
     (a'₁₃ = 0) ->
      (k7 a'₁₃) ->
       ∀ (a'₁₄ : Int),
        (a'₁₄ = 0) ->
         (k8 a'₁₄) ->
          ∀ (a'₁₅ : Int),
           ((k9 a'₁₅)) ->
            (a'₁₅ > 0))
 
end F
