import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure Pred  where
  mkPred₀ ::
    is_atom : Prop 
    nnf : Prop 
  deriving Inhabited
attribute [grind .] Pred.ext


end F
