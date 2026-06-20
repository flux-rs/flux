import Detached.DetachImpl00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestB := 
 (0 ≤ (0 + 1)) ->
  (0 ≤ ((0 + 1) + 1)) ->
   (0 ≤ (((0 + 1) + 1) + 1)) ->
    ((((0 + 1) + 1) + 1) = 3)
end F
