import Enums.Option00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def MyUnwrap := 
 (True = False) ->
  False
end F
