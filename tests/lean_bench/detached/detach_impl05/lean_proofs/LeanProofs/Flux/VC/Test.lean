import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.WrapperRole
import LeanFixpoint
open Classical

namespace F



def Test := 
 ((((WrapperRole.mkWrapperRole₀) = (WrapperRole.mkWrapperRole₀)) = True)) ∧
 ((((WrapperRole.mkWrapperRole₀) = (WrapperRole.mkWrapperRole₀)) = True)) ∧
 (∀ (v₀ : Prop),
  (v₀ <-> ((WrapperRole.mkWrapperRole₀) ≠ (WrapperRole.mkWrapperRole₁))) ->
   (v₀ = True))
 
end F
