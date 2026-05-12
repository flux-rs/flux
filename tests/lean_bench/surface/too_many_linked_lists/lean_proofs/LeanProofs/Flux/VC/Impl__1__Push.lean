import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__1__Push := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (elem₀ : Int),
   (n₀ ≥ 0) ->
    (((k0 n₀ n₀ elem₀))) ∧
    (∀ (a'₁ : Int),
     ((k0 a'₁ n₀ elem₀)) ->
      (a'₁ ≥ 0) ->
       (((a'₁ + 1) ≥ 0)) ∧
       (((a'₁ + 1) = (n₀ + 1)))
       )
    
end F
