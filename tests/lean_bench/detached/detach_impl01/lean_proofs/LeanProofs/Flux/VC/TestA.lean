import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestA := 
 (0 ≤ (0 + 1)) ->
  (0 ≤ ((0 + 1) + 1)) ->
   (0 ≤ (((0 + 1) + 1) + 1)) ->
    ((((0 + 1) + 1) + 1) = 3)
end F
