import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure SliceIterIter  where
  mkSliceIterIter₀ ::
    idx : Int
    len : Int

instance : Inhabited SliceIterIter where
  default := ⟨default, default⟩
end F
