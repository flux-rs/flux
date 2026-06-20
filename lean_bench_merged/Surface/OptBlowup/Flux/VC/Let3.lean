import Surface.OptBlowup.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Let3 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (n₀ : Int),
  ∀ (a'₀ : Int),
   (n₀ < a'₀) ->
    ∀ (a'₁ : Int),
     (a'₀ < a'₁) ->
      ∀ (a'₂ : Int),
       (a'₁ < a'₂) ->
        (((k0 a'₂ n₀ a'₀ a'₁ a'₂))) ∧
        (∀ (a'₃ : Int),
         ((k0 a'₃ n₀ a'₀ a'₁ a'₂)) ->
          (n₀ < a'₃))
        
end F
