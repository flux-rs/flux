import Enums.Opt01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def IsSome := ∃ k0 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> Prop, 
 ∀ (b₀ : Prop),
  ((b₀ = False) ->
   ((k0 False False b₀))) ∧
  ((b₀ = True) ->
   ∀ (a'₀ : Int),
    ((k0 True True b₀))) ∧
  (∀ (x₀ : Prop),
   ∀ (a'₂ : Prop),
    ((k0 x₀ a'₂ b₀)) ->
     (a'₂ = b₀))
  
end F
