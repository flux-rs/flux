import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def IsSome := 
 ∀ (b₀ : Prop),
  ((b₀ = False) ->
   (False = b₀)) ∧
  ((b₀ = True) ->
   (True = b₀))
  
end F
