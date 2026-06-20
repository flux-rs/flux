import Surface.TryFrom00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__0__TryFrom := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (x₀ : Int),
  (((k0 x₀ x₀))) ∧
  (∀ (a'₀ : Int),
   ((k0 a'₀ x₀)) ->
    (x₀ = a'₀))
  
end F
