import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := 
 (0 ≤ (0 + 1)) ->
  (0 ≤ ((0 + 1) + 1)) ->
   (0 ≤ (((0 + 1) + 1) + 1)) ->
    (0 ≤ ((((0 + 1) + 1) + 1) + 2)) ->
     (((((0 + 1) + 1) + 1) + 2) = 5)
end F
