import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def MyUnwrap := 
 (True = False) ->
  False
end F
