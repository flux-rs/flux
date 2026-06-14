import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

inductive Gib  where
|  mkGib₀ 
|  mkGib₁ 
deriving Inhabited


end F
