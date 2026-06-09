import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__0__LenConstMemory := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (((k0 0 n₀ n₀))) ∧
  (∀ (len₀ : Int),
   ∀ (cur₀ : Int),
    ((k0 len₀ cur₀ n₀)) ->
     (∀ (n₁ : Int),
      (cur₀ = (n₁ + 1)) ->
       ∀ (a'₃ : Int),
        ((k0 (len₀ + 1) n₁ n₀))) ∧
     ((cur₀ = 0) ->
      (len₀ = n₀))
     )
  
end F
