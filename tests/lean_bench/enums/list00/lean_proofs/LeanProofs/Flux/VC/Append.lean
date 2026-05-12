import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Append := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (n1₀ : Int),
  ∀ (n2₀ : Int),
   (n1₀ ≥ 0) ->
    (n2₀ ≥ 0) ->
     ((n1₀ = 0) ->
      ((k0 n2₀ n1₀ n2₀))) ∧
     (∀ (n₀ : Int),
      (n1₀ = (n₀ + 1)) ->
       ∀ (a'₁ : Int),
        (n₀ ≥ 0) ->
         ((n₀ + n2₀) ≥ 0) ->
          (((k1 (n₀ + n2₀) n1₀ n2₀ n₀ a'₁))) ∧
          (∀ (a'₂ : Int),
           ((k1 a'₂ n1₀ n2₀ n₀ a'₁)) ->
            (a'₂ ≥ 0) ->
             ((k0 (a'₂ + 1) n1₀ n2₀)))
          ) ∧
     (∀ (a'₃ : Int),
      ((k0 a'₃ n1₀ n2₀)) ->
       (a'₃ = (n1₀ + n2₀)))
     
end F
