import Surface.Rmat.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__0__Get := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (m₀ : Int),
  ∀ (n₀ : Int),
   ∀ (v₀ : Int),
    ∀ (v₁ : Int),
     (v₀ < m₀) ->
      (v₁ < n₀) ->
       (v₀ ≥ 0) ->
        (v₁ ≥ 0) ->
         (n₀ ≥ 0) ->
          (0 ≤ m₀) ->
           (∀ (a'₂ : Int),
            (a'₂ = n₀) ->
             ((k0 a'₂ m₀ n₀ v₀ v₁))) ∧
           (∀ (a'₃ : Int),
            ((k0 a'₃ m₀ n₀ v₀ v₁)) ->
             (0 ≤ a'₃) ->
              (v₁ < a'₃))
           
end F
