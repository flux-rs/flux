import Surface.Date.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := 
 False ->
  False ->
   (((1977 % 400) = 0) ∨ (((1977 % 4) = 0) ∧ ((1977 % 100) > 0)))
end F
