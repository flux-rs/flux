import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test0 := 
 ((c0 1 2) = (4 * 1)) ->
  (((c0 1 2) = 4) = True)
end F
