import Surface.Closure06.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test001Client := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((k1 (a'₀ + 1) a'₀))) ∧
 (∀ (v₀ : Int),
  (10 ≤ v₀) ->
   (((k0 v₀))) ∧
   (∀ (a'₂ : Int),
    ((k1 a'₂ v₀)) ->
     (10 ≤ a'₂))
   )
 
end F
