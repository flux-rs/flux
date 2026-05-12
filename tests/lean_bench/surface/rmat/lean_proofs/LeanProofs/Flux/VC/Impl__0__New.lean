import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Impl__0__New := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (rows₀ : Int),
  ∀ (cols₀ : Int),
   (rows₀ ≥ 0) ->
    (cols₀ ≥ 0) ->
     (((k0 0 0 rows₀ cols₀))) ∧
     (∀ (inner₀ : Int),
      ∀ (i₀ : Int),
       ((k0 inner₀ i₀ rows₀ cols₀)) ->
        ((¬(i₀ < rows₀)) ->
         (∀ (a'₂ : Int),
          ((k1 a'₂ inner₀ i₀ rows₀ cols₀)) ->
           (a'₂ = cols₀)) ∧
         ((inner₀ = rows₀))
         ) ∧
        ((i₀ < rows₀) ->
         (0 ≤ cols₀) ->
          (∀ (a'₃ : Int),
           ((k1 a'₃ inner₀ i₀ rows₀ cols₀)) ->
            ((k2 a'₃ rows₀ cols₀ inner₀ i₀))) ∧
          (((k2 cols₀ rows₀ cols₀ inner₀ i₀))) ∧
          ((0 ≤ (inner₀ + 1)) ->
           (((k0 (inner₀ + 1) (i₀ + 1) rows₀ cols₀))) ∧
           (∀ (a'₄ : Int),
            ((k2 a'₄ rows₀ cols₀ inner₀ i₀)) ->
             ((k1 a'₄ (inner₀ + 1) (i₀ + 1) rows₀ cols₀)))
           )
          )
        )
     
end F
