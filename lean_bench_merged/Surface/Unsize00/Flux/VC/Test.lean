import Surface.Unsize00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := 
 (0 ≤ (0 + 1)) ->
  (0 ≤ ((0 + 1) + 1)) ->
   (0 ≤ (((0 + 1) + 1) + 1)) ->
    (0 ≤ ((((0 + 1) + 1) + 1) + 2)) ->
     (((((0 + 1) + 1) + 1) + 2) = 5)
end F
