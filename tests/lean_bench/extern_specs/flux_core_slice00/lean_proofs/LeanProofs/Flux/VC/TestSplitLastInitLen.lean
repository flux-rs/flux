import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestSplitLastInitLen := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (∀ (xs_elem₀ : Int),
    ((k0 xs_elem₀ a'₀))) ∧
   (((a'₀ ≠ 0) = True) ->
    ∀ (a'₂ : Int),
     ((k0 a'₂ a'₀)) ->
      ((a'₀ - 1) ≥ 0) ->
       (((a'₀ - 1) = (a'₀ - 1)) = True))
   
end F
