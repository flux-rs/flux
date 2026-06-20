import Enums.Issue234.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := 
 ∀ (x₀ : Int),
  ((x₀ = 1) ->
   (1 = x₀)) ∧
  ((x₀ = 3) ->
   (3 = x₀)) ∧
  ((x₀ = 2) ->
   (2 = x₀))
  
end F
