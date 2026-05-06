import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test02 := ∃ k0 : (a0 : Prop) -> Prop, 
 (∀ (a'₀ : Int),
  ((k0 True))) ∧
 (∀ (a'₁ : Prop),
  ((k0 a'₁)) ->
   (a'₁ = True))
 
end F
