import Surface.Closure12.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestVecOfNat := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (∀ (a'₀ : Int),
    ((k0 a'₀ n₀)) ->
     (a'₀ ≥ 0) ->
      ((k1 10 a'₀ n₀))) ∧
   (∀ (v₀ : Int),
    ((0 ≤ v₀) ∧ (v₀ < n₀)) ->
     (((k0 v₀ n₀))) ∧
     (∀ (a'₂ : Int),
      ((k1 a'₂ v₀ n₀)) ->
       ((k2 a'₂ n₀)))
     ) ∧
   ((0 ≤ n₀) ->
    ∀ (a'₃ : Int),
     ((k2 a'₃ n₀)) ->
      (0 ≤ a'₃))
   
end F
