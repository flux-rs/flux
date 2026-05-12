import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := 
 ((((1 + 1) = 2) = True)) ∧
 (((1 + 2) ≥ 0) ->
  (((1 + 2) = 3) = True))
 
end F
