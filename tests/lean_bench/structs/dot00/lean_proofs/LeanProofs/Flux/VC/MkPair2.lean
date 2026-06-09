import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def MkPair2 := 
 ∀ (a₀ : Int),
  ∀ (b₀ : Int),
   ((a₀ = a₀)) ∧
   ((b₀ = b₀))
   
end F
