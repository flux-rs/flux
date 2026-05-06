import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test02 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((k0 0 1))) ∧
 (∀ (a'₀ : Int),
  ∀ (a'₁ : Int),
   (((k0 a'₀ a'₁)) ->
    (a'₀ < a'₁)) ∧
   ((a'₀ < a'₁) ->
    ((k0 a'₀ a'₁)))
   )
 
end F
