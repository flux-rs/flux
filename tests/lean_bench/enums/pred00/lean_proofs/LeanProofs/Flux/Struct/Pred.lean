import LeanProofs.Flux.Prelude
open Classical

namespace F

@[ext]
structure Pred  where
  mkPred₀ ::
    is_atom : Prop 
    nnf : Prop 


end F
