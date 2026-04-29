import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.Pred
import LeanFixpoint
open Classical

namespace F



def Impl__IntoNnf := ∃ k0 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> Prop, ∃ k3 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> Prop, ∃ k4 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Int) -> Prop, ∃ k5 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Prop) -> Prop, ∃ k6 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Prop) -> (a14 : Prop) -> (a15 : Prop) -> Prop, ∃ k7 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Prop) -> Prop, ∃ k8 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Prop) -> (a14 : Prop) -> (a15 : Prop) -> Prop, ∃ k9 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> Prop, ∃ k10 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Prop) -> Prop, ∃ k11 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> Prop, ∃ k12 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Prop) -> Prop, 
 ∀ (self₀ : Pred),
  ((Pred.is_atom self₀) -> (Pred.nnf self₀)) ->
   ((self₀ = (Pred.mkPred₀ True True)) ->
    ((k0 True True (Pred.is_atom self₀) (Pred.nnf self₀)))) ∧
   ((self₀ = (Pred.mkPred₀ True True)) ->
    ((k0 True True (Pred.is_atom self₀) (Pred.nnf self₀)))) ∧
   ((self₀ = (Pred.mkPred₀ True True)) ->
    ∀ (a'₁ : Int),
     ((k0 True True (Pred.is_atom self₀) (Pred.nnf self₀)))) ∧
   (∀ (p₀ : Pred),
    (self₀ = (Pred.mkPred₀ False (Pred.is_atom p₀))) ->
     ((Pred.is_atom p₀) -> (Pred.nnf p₀)) ->
      ((p₀ = (Pred.mkPred₀ True True)) ->
       (((k1 True True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀)))) ∧
       (∀ (a'₃ : Pred),
        ((k1 (Pred.is_atom a'₃) (Pred.nnf a'₃) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀))) ->
         ((Pred.is_atom a'₃) -> (Pred.nnf a'₃)) ->
          ((k2 False (Pred.is_atom a'₃) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀))))
       ) ∧
      ((p₀ = (Pred.mkPred₀ True True)) ->
       (((k3 True True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀)))) ∧
       (∀ (a'₄ : Pred),
        ((k3 (Pred.is_atom a'₄) (Pred.nnf a'₄) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀))) ->
         ((Pred.is_atom a'₄) -> (Pred.nnf a'₄)) ->
          ((k2 False (Pred.is_atom a'₄) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀))))
       ) ∧
      ((p₀ = (Pred.mkPred₀ True True)) ->
       ∀ (a'₅ : Int),
        (((k4 True True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) a'₅))) ∧
        (∀ (a'₆ : Pred),
         ((k4 (Pred.is_atom a'₆) (Pred.nnf a'₆) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) a'₅)) ->
          ((Pred.is_atom a'₆) -> (Pred.nnf a'₆)) ->
           ((k2 False (Pred.is_atom a'₆) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀))))
        ) ∧
      (∀ (p₁ : Pred),
       (p₀ = (Pred.mkPred₀ False (Pred.is_atom p₁))) ->
        ((Pred.is_atom p₁) -> (Pred.nnf p₁)) ->
         ∀ (v₀ : Pred),
          (Pred.nnf v₀) ->
           ((Pred.is_atom v₀) -> True) ->
            ((k2 (Pred.is_atom v₀) True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀)))) ∧
      (∀ (p1₀ : Pred),
       ∀ (p2₀ : Pred),
        (p₀ = (Pred.mkPred₀ False ((Pred.nnf p1₀) ∧ (Pred.nnf p2₀)))) ->
         ((Pred.is_atom p1₀) -> (Pred.nnf p1₀)) ->
          ((Pred.is_atom p2₀) -> (Pred.nnf p2₀)) ->
           ∀ (p1₁ : Pred),
            (Pred.nnf p1₁) ->
             ((Pred.is_atom p1₁) -> True) ->
              ∀ (p2₁ : Pred),
               (Pred.nnf p2₁) ->
                ((Pred.is_atom p2₁) -> True) ->
                 (((k5 (Pred.is_atom p1₁) True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) (Pred.is_atom p1₀) (Pred.nnf p1₀) (Pred.is_atom p2₀) (Pred.nnf p2₀) (Pred.is_atom p1₁) True (Pred.is_atom p2₁) True))) ∧
                 (∀ (a'₁₃ : Pred),
                  ((k5 (Pred.is_atom a'₁₃) (Pred.nnf a'₁₃) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) (Pred.is_atom p1₀) (Pred.nnf p1₀) (Pred.is_atom p2₀) (Pred.nnf p2₀) (Pred.is_atom p1₁) True (Pred.is_atom p2₁) True)) ->
                   ((Pred.is_atom a'₁₃) -> (Pred.nnf a'₁₃)) ->
                    (((k6 (Pred.is_atom p2₁) True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) (Pred.is_atom p1₀) (Pred.nnf p1₀) (Pred.is_atom p2₀) (Pred.nnf p2₀) (Pred.is_atom p1₁) True (Pred.is_atom p2₁) True (Pred.is_atom a'₁₃) (Pred.nnf a'₁₃)))) ∧
                    (∀ (a'₁₄ : Pred),
                     ((k6 (Pred.is_atom a'₁₄) (Pred.nnf a'₁₄) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) (Pred.is_atom p1₀) (Pred.nnf p1₀) (Pred.is_atom p2₀) (Pred.nnf p2₀) (Pred.is_atom p1₁) True (Pred.is_atom p2₁) True (Pred.is_atom a'₁₃) (Pred.nnf a'₁₃))) ->
                      ((Pred.is_atom a'₁₄) -> (Pred.nnf a'₁₄)) ->
                       ((k2 False ((Pred.nnf a'₁₃) ∧ (Pred.nnf a'₁₄)) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀))))
                    )
                 ) ∧
      (∀ (p1₂ : Pred),
       ∀ (p2₂ : Pred),
        (p₀ = (Pred.mkPred₀ False ((Pred.nnf p1₂) ∧ (Pred.nnf p2₂)))) ->
         ((Pred.is_atom p1₂) -> (Pred.nnf p1₂)) ->
          ((Pred.is_atom p2₂) -> (Pred.nnf p2₂)) ->
           ∀ (p1₃ : Pred),
            (Pred.nnf p1₃) ->
             ((Pred.is_atom p1₃) -> True) ->
              ∀ (p2₃ : Pred),
               (Pred.nnf p2₃) ->
                ((Pred.is_atom p2₃) -> True) ->
                 (((k7 (Pred.is_atom p1₃) True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom p1₃) True (Pred.is_atom p2₃) True))) ∧
                 (∀ (a'₁₉ : Pred),
                  ((k7 (Pred.is_atom a'₁₉) (Pred.nnf a'₁₉) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom p1₃) True (Pred.is_atom p2₃) True)) ->
                   ((Pred.is_atom a'₁₉) -> (Pred.nnf a'₁₉)) ->
                    (((k8 (Pred.is_atom p2₃) True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom p1₃) True (Pred.is_atom p2₃) True (Pred.is_atom a'₁₉) (Pred.nnf a'₁₉)))) ∧
                    (∀ (a'₂₀ : Pred),
                     ((k8 (Pred.is_atom a'₂₀) (Pred.nnf a'₂₀) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀) (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom p1₃) True (Pred.is_atom p2₃) True (Pred.is_atom a'₁₉) (Pred.nnf a'₁₉))) ->
                      ((Pred.is_atom a'₂₀) -> (Pred.nnf a'₂₀)) ->
                       ((k2 False ((Pred.nnf a'₁₉) ∧ (Pred.nnf a'₂₀)) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀))))
                    )
                 ) ∧
      (∀ (a'₂₁ : Pred),
       ((k2 (Pred.is_atom a'₂₁) (Pred.nnf a'₂₁) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p₀) (Pred.nnf p₀))) ->
        ((k0 (Pred.is_atom a'₂₁) (Pred.nnf a'₂₁) (Pred.is_atom self₀) (Pred.nnf self₀))))
      ) ∧
   (∀ (p1₄ : Pred),
    ∀ (p2₄ : Pred),
     (self₀ = (Pred.mkPred₀ False ((Pred.nnf p1₄) ∧ (Pred.nnf p2₄)))) ->
      ((Pred.is_atom p1₄) -> (Pred.nnf p1₄)) ->
       ((Pred.is_atom p2₄) -> (Pred.nnf p2₄)) ->
        ∀ (v₁ : Pred),
         (Pred.nnf v₁) ->
          ((Pred.is_atom v₁) -> True) ->
           (((k9 (Pred.is_atom v₁) True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p1₄) (Pred.nnf p1₄) (Pred.is_atom p2₄) (Pred.nnf p2₄) (Pred.is_atom v₁) True))) ∧
           (∀ (a'₂₅ : Pred),
            ((k9 (Pred.is_atom a'₂₅) (Pred.nnf a'₂₅) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p1₄) (Pred.nnf p1₄) (Pred.is_atom p2₄) (Pred.nnf p2₄) (Pred.is_atom v₁) True)) ->
             ((Pred.is_atom a'₂₅) -> (Pred.nnf a'₂₅)) ->
              ∀ (v₂ : Pred),
               (Pred.nnf v₂) ->
                ((Pred.is_atom v₂) -> True) ->
                 (((k10 (Pred.is_atom v₂) True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p1₄) (Pred.nnf p1₄) (Pred.is_atom p2₄) (Pred.nnf p2₄) (Pred.is_atom v₁) True (Pred.is_atom a'₂₅) (Pred.nnf a'₂₅) (Pred.is_atom v₂) True))) ∧
                 (∀ (a'₂₇ : Pred),
                  ((k10 (Pred.is_atom a'₂₇) (Pred.nnf a'₂₇) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p1₄) (Pred.nnf p1₄) (Pred.is_atom p2₄) (Pred.nnf p2₄) (Pred.is_atom v₁) True (Pred.is_atom a'₂₅) (Pred.nnf a'₂₅) (Pred.is_atom v₂) True)) ->
                   ((Pred.is_atom a'₂₇) -> (Pred.nnf a'₂₇)) ->
                    ((k0 False ((Pred.nnf a'₂₅) ∧ (Pred.nnf a'₂₇)) (Pred.is_atom self₀) (Pred.nnf self₀))))
                 )
           ) ∧
   (∀ (p1₅ : Pred),
    ∀ (p2₅ : Pred),
     (self₀ = (Pred.mkPred₀ False ((Pred.nnf p1₅) ∧ (Pred.nnf p2₅)))) ->
      ((Pred.is_atom p1₅) -> (Pred.nnf p1₅)) ->
       ((Pred.is_atom p2₅) -> (Pred.nnf p2₅)) ->
        ∀ (v₃ : Pred),
         (Pred.nnf v₃) ->
          ((Pred.is_atom v₃) -> True) ->
           (((k11 (Pred.is_atom v₃) True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p1₅) (Pred.nnf p1₅) (Pred.is_atom p2₅) (Pred.nnf p2₅) (Pred.is_atom v₃) True))) ∧
           (∀ (a'₃₁ : Pred),
            ((k11 (Pred.is_atom a'₃₁) (Pred.nnf a'₃₁) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p1₅) (Pred.nnf p1₅) (Pred.is_atom p2₅) (Pred.nnf p2₅) (Pred.is_atom v₃) True)) ->
             ((Pred.is_atom a'₃₁) -> (Pred.nnf a'₃₁)) ->
              ∀ (v₄ : Pred),
               (Pred.nnf v₄) ->
                ((Pred.is_atom v₄) -> True) ->
                 (((k12 (Pred.is_atom v₄) True (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p1₅) (Pred.nnf p1₅) (Pred.is_atom p2₅) (Pred.nnf p2₅) (Pred.is_atom v₃) True (Pred.is_atom a'₃₁) (Pred.nnf a'₃₁) (Pred.is_atom v₄) True))) ∧
                 (∀ (a'₃₃ : Pred),
                  ((k12 (Pred.is_atom a'₃₃) (Pred.nnf a'₃₃) (Pred.is_atom self₀) (Pred.nnf self₀) (Pred.is_atom p1₅) (Pred.nnf p1₅) (Pred.is_atom p2₅) (Pred.nnf p2₅) (Pred.is_atom v₃) True (Pred.is_atom a'₃₁) (Pred.nnf a'₃₁) (Pred.is_atom v₄) True)) ->
                   ((Pred.is_atom a'₃₃) -> (Pred.nnf a'₃₃)) ->
                    ((k0 False ((Pred.nnf a'₃₁) ∧ (Pred.nnf a'₃₃)) (Pred.is_atom self₀) (Pred.nnf self₀))))
                 )
           ) ∧
   (∀ (a'₃₄ : Pred),
    ((k0 (Pred.is_atom a'₃₄) (Pred.nnf a'₃₄) (Pred.is_atom self₀) (Pred.nnf self₀))) ->
     (Pred.nnf a'₃₄))
   
end F
