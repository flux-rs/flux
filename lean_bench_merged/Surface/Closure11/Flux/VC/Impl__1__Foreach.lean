import Surface.Closure11.Flux.Prelude
import Surface.Closure11.Flux.Struct.OpsRangeRange
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__1__Foreach := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (c0 : Prop),
  ∀ (s₀ : (OpsRangeRange Int)),
   ∀ (f₀ : Int),
    ((OpsRangeRange.start s₀) ≥ 0) ->
     ((OpsRangeRange.end_ s₀) ≥ 0) ->
      (((k0 f₀ (OpsRangeRange.start s₀) (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀))) ∧
      (∀ (f₁ : Int),
       ∀ (i₀ : Int),
        ((k0 f₁ i₀ (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀)) ->
         (i₀ < (OpsRangeRange.end_ s₀)) ->
          (∀ (a'₃ : Int),
           ((k1 a'₃ (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀ f₁ i₀)) ->
            ∀ (a'₄ : Int),
             ((k2 a'₄ (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀ f₁ i₀)) ->
              ((((OpsRangeRange.start s₀) ≤ a'₄)) ∧
              ((a'₄ < (OpsRangeRange.end_ s₀)))
              ) ∧
              (∀ (a'₅ : Int),
               ((k1 a'₅ (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀ f₁ i₀)) ->
                ∀ (a'₆ : Int),
                 ((k2 a'₆ (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀ f₁ i₀)) ->
                  ((((OpsRangeRange.start s₀) ≤ a'₆)) ∧
                  ((a'₆ < (OpsRangeRange.end_ s₀)))
                  ) ∧
                  (((k3 (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀ f₁ i₀)))
                  )
              ) ∧
          (False ->
           ((c0) ∨ False)) ∧
          (((k1 f₁ (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀ f₁ i₀))) ∧
          (((k2 i₀ (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀ f₁ i₀))) ∧
          (((k3 (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀ f₁ i₀)) ->
           ∀ (a'₇ : Int),
            ((k1 a'₇ (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀ f₁ i₀)) ->
             ((k0 a'₇ (i₀ + 1) (OpsRangeRange.start s₀) (OpsRangeRange.end_ s₀) f₀)))
          )
      
end F
