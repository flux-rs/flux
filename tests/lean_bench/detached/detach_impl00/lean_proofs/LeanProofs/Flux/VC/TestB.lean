import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestB := 
 (0 ≤ (0 + 1)) ->
  (0 ≤ ((0 + 1) + 1)) ->
   (0 ≤ (((0 + 1) + 1) + 1)) ->
    ((((0 + 1) + 1) + 1) = 3)
end F
