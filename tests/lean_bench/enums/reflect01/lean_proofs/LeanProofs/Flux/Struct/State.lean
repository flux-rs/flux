import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

inductive State  where
|  mkState₀ 
|  mkState₁ 
deriving Inhabited


end F
