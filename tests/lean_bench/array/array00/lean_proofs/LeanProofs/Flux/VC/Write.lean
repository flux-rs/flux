import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Write := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 10))) ∧
 (((k0 20))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ∀ (a'₁ : Int),
    ((k0 a'₁)) ->
     ((a'₀ + a'₁) > 10))
 
end F
