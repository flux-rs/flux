import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.S2
open Classical
set_option linter.unusedVariables false


namespace F



def Test03 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> Prop, 
 ∀ (x₀ : S2),
  ∀ (y₀ : S2),
   (((k0 (S2.a x₀) (S2.b x₀) (S2.a x₀) (S2.b x₀) (S2.a y₀) (S2.b y₀)))) ∧
   (((k0 (S2.a y₀) (S2.b y₀) (S2.a x₀) (S2.b x₀) (S2.a y₀) (S2.b y₀)))) ∧
   (∀ (a'₂ : S2),
    ((k0 (S2.a a'₂) (S2.b a'₂) (S2.a x₀) (S2.b x₀) (S2.a y₀) (S2.b y₀))) ->
     ∀ (a'₃ : Int),
      ∀ (a'₄ : S2),
       ((k0 (S2.a a'₄) (S2.b a'₄) (S2.a x₀) (S2.b x₀) (S2.a y₀) (S2.b y₀))) ->
        ∀ (a'₅ : S2),
         ((k0 (S2.a a'₅) (S2.b a'₅) (S2.a x₀) (S2.b x₀) (S2.a y₀) (S2.b y₀))) ->
          ∀ (v₀ : Int),
           (v₀ > 0) ->
            ∀ (a'₇ : S2),
             ((k0 (S2.a a'₇) (S2.b a'₇) (S2.a x₀) (S2.b x₀) (S2.a y₀) (S2.b y₀))) ->
              ((v₀ + 1) > 0))
   
end F
