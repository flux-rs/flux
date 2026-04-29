import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestMod := 
 (((3 % 2) = 1)) ∧
 ((((5 % 2) = 1)) ∧
 (((27 % 2) = 1))
 )
 
end F
