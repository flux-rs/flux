import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__LenConstMemory := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (((k0 n₀ 0 n₀))) ∧
  (∀ (cur₀ : Int),
   ∀ (len₀ : Int),
    ((k0 cur₀ len₀ n₀)) ->
     (∀ (n₁ : Int),
      (cur₀ = (n₁ + 1)) ->
       ∀ (a'₃ : Int),
        ((k0 n₁ (len₀ + 1) n₀))) ∧
     ((cur₀ = 0) ->
      (len₀ = n₀))
     )
  
end F
