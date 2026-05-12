import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Unwrap := 
 (True = False) ->
  False
end F
