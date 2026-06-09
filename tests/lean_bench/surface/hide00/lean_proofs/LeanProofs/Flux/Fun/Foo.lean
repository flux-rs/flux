import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Mod33
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def foo (a'₁ : Int) (a'₂ : Int) : Prop :=
  ((mod33 a'₁) = a'₂)


end F
