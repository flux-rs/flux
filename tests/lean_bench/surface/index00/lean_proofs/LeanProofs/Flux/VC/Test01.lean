import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test01 := 
 ((5 + 1) ≥ 0) ->
  (((5 + 1) = 6) = True)
end F
