import Surface.Gcd.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Gcd := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ∀ (v₀ : Int),
  ∀ (v₁ : Int),
   (v₀ > 0) ->
    (v₁ > 0) ->
     (((k0 v₀ v₁ v₀ v₁))) ∧
     (∀ (a₀ : Int),
      ∀ (b₀ : Int),
       ((k0 a₀ b₀ v₀ v₁)) ->
        ((b₀ ≠ 0)) ∧
        ((b₀ ≠ 0) ->
         ((¬((b₀ = (-1)) ∧ (a₀ = (-2147483648))))) ∧
         ((¬((b₀ = (-1)) ∧ (a₀ = (-2147483648)))) ->
          ∀ (a'₄ : Int),
           (((a₀ ≥ 0) ∧ (b₀ ≥ 0)) -> (a'₄ = (a₀ % b₀))) ->
            ((¬(a'₄ > 0)) ->
             (b₀ > 0)) ∧
            ((a'₄ > 0) ->
             ((b₀ ≠ 0)) ∧
             ((b₀ ≠ 0) ->
              ∀ (a'₅ : Int),
               (((a₀ ≥ 0) ∧ (b₀ ≥ 0)) -> (a'₅ = (a₀ % b₀))) ->
                ((k0 b₀ a'₅ v₀ v₁)))
             )
            )
         )
        )
     
end F
