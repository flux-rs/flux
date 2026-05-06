import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test1 := 
 ((c0 1 2) = (4 * 1)) ->
  ((c0 (c0 1 2) 2) = (4 * (c0 1 2))) ->
   (((c0 (c0 1 2) 2) = 16) = True)
end F
