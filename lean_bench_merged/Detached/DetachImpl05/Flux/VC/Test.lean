import Detached.DetachImpl05.Flux.Prelude
import Detached.DetachImpl05.Flux.Struct.WrapperRole
open Classical
set_option linter.unusedVariables false


namespace F



def Test := 
 ((((WrapperRole.mkWrapperRole₀) = (WrapperRole.mkWrapperRole₀)) = True)) ∧
 ((((WrapperRole.mkWrapperRole₀) = (WrapperRole.mkWrapperRole₀)) = True)) ∧
 (∀ (v₀ : Prop),
  (v₀ <-> ((WrapperRole.mkWrapperRole₀) ≠ (WrapperRole.mkWrapperRole₁))) ->
   (v₀ = True))
 
end F
