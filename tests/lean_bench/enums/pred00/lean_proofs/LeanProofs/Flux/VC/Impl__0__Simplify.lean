import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.Pred
import LeanFixpoint
open Classical

namespace F



def Impl__0__Simplify := ∃ k0 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Int) -> Prop, ∃ k3 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> Prop, ∃ k4 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> Prop, ∃ k5 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Prop) -> Prop, ∃ k6 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> Prop, ∃ k7 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> Prop, ∃ k8 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Prop) -> Prop, 
 ∀ (v₀ : Pred),
  (Pred.nnf v₀) ->
   ((Pred.is_atom v₀) -> True) ->
    ((v₀ = (Pred.mkPred₀ True True)) ->
     ((k0 True True (Pred.is_atom v₀) True))) ∧
    ((v₀ = (Pred.mkPred₀ True True)) ->
     ((k0 True True (Pred.is_atom v₀) True))) ∧
    ((v₀ = (Pred.mkPred₀ True True)) ->
     ∀ (a'₁ : Int),
      ((k0 True True (Pred.is_atom v₀) True))) ∧
    (∀ (p₀ : Pred),
     (v₀ = (Pred.mkPred₀ False (Pred.is_atom p₀))) ->
      ((Pred.is_atom p₀) -> (Pred.nnf p₀)) ->
       ((p₀ = (Pred.mkPred₀ True True)) ->
        ((k1 True True True True (Pred.is_atom v₀) True (Pred.is_atom p₀) (Pred.nnf p₀)))) ∧
       ((p₀ = (Pred.mkPred₀ True True)) ->
        ((k1 True True True True (Pred.is_atom v₀) True (Pred.is_atom p₀) (Pred.nnf p₀)))) ∧
       ((p₀ = (Pred.mkPred₀ True True)) ->
        ∀ (a'₃ : Int),
         (((k2 True True (Pred.is_atom v₀) True (Pred.is_atom p₀) (Pred.nnf p₀) a'₃))) ∧
         (∀ (a'₄ : Pred),
          ((k2 (Pred.is_atom a'₄) (Pred.nnf a'₄) (Pred.is_atom v₀) True (Pred.is_atom p₀) (Pred.nnf p₀) a'₃)) ->
           ((Pred.is_atom a'₄) -> (Pred.nnf a'₄)) ->
            ((k1 False (Pred.is_atom a'₄) True True (Pred.is_atom v₀) True (Pred.is_atom p₀) (Pred.nnf p₀))))
         ) ∧
       (∀ (p₁ : Pred),
        (p₀ = (Pred.mkPred₀ False (Pred.is_atom p₁))) ->
         ((Pred.is_atom p₁) -> (Pred.nnf p₁)) ->
          False) ∧
       (∀ (p1₀ : Pred),
        ∀ (p2₀ : Pred),
         (p₀ = (Pred.mkPred₀ False ((Pred.nnf p1₀) ∧ (Pred.nnf p2₀)))) ->
          ((Pred.is_atom p1₀) -> (Pred.nnf p1₀)) ->
           ((Pred.is_atom p2₀) -> (Pred.nnf p2₀)) ->
            False) ∧
       (∀ (p1₁ : Pred),
        ∀ (p2₁ : Pred),
         (p₀ = (Pred.mkPred₀ False ((Pred.nnf p1₁) ∧ (Pred.nnf p2₁)))) ->
          ((Pred.is_atom p1₁) -> (Pred.nnf p1₁)) ->
           ((Pred.is_atom p2₁) -> (Pred.nnf p2₁)) ->
            False) ∧
       (∀ (a'₁₀ : Pred),
        ∀ (a'₁₁ : Prop),
         ∀ (a'₁₂ : Prop),
          ((k1 (Pred.is_atom a'₁₀) (Pred.nnf a'₁₀) a'₁₁ a'₁₂ (Pred.is_atom v₀) True (Pred.is_atom p₀) (Pred.nnf p₀))) ->
           ((k0 (Pred.is_atom a'₁₀) (Pred.nnf a'₁₀) (Pred.is_atom v₀) True)))
       ) ∧
    (∀ (p1₂ : Pred),
     ∀ (p2₂ : Pred),
      (v₀ = (Pred.mkPred₀ False ((Pred.nnf p1₂) ∧ (Pred.nnf p2₂)))) ->
       ((Pred.is_atom p1₂) -> (Pred.nnf p1₂)) ->
        ((Pred.is_atom p2₂) -> (Pred.nnf p2₂)) ->
         ((Pred.nnf p1₂)) ∧
         (∀ (v₁ : Pred),
          (Pred.nnf v₁) ->
           ((Pred.is_atom v₁) -> True) ->
            ((Pred.nnf p2₂)) ∧
            (∀ (v₂ : Pred),
             (Pred.nnf v₂) ->
              ((Pred.is_atom v₂) -> True) ->
               ((v₁ = (Pred.mkPred₀ True True)) ->
                ((k3 (Pred.is_atom v₂) True (Pred.is_atom v₀) True (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom v₁) True (Pred.is_atom v₂) True))) ∧
               ((v₁ = (Pred.mkPred₀ True True)) ->
                ((k3 True True (Pred.is_atom v₀) True (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom v₁) True (Pred.is_atom v₂) True))) ∧
               (((k4 (Pred.is_atom v₁) True (Pred.is_atom v₀) True (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom v₁) True (Pred.is_atom v₂) True))) ∧
               (∀ (a'₁₇ : Pred),
                ((k4 (Pred.is_atom a'₁₇) (Pred.nnf a'₁₇) (Pred.is_atom v₀) True (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom v₁) True (Pred.is_atom v₂) True)) ->
                 ((Pred.is_atom a'₁₇) -> (Pred.nnf a'₁₇)) ->
                  (((k5 (Pred.is_atom v₂) True (Pred.is_atom v₀) True (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom v₁) True (Pred.is_atom v₂) True (Pred.is_atom a'₁₇) (Pred.nnf a'₁₇)))) ∧
                  (∀ (a'₁₈ : Pred),
                   ((k5 (Pred.is_atom a'₁₈) (Pred.nnf a'₁₈) (Pred.is_atom v₀) True (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom v₁) True (Pred.is_atom v₂) True (Pred.is_atom a'₁₇) (Pred.nnf a'₁₇))) ->
                    ((Pred.is_atom a'₁₈) -> (Pred.nnf a'₁₈)) ->
                     ((k3 False ((Pred.nnf a'₁₇) ∧ (Pred.nnf a'₁₈)) (Pred.is_atom v₀) True (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom v₁) True (Pred.is_atom v₂) True)))
                  ) ∧
               (∀ (a'₁₉ : Pred),
                ((k3 (Pred.is_atom a'₁₉) (Pred.nnf a'₁₉) (Pred.is_atom v₀) True (Pred.is_atom p1₂) (Pred.nnf p1₂) (Pred.is_atom p2₂) (Pred.nnf p2₂) (Pred.is_atom v₁) True (Pred.is_atom v₂) True)) ->
                 ((k0 (Pred.is_atom a'₁₉) (Pred.nnf a'₁₉) (Pred.is_atom v₀) True)))
               )
            )
         ) ∧
    (∀ (p1₃ : Pred),
     ∀ (p2₃ : Pred),
      (v₀ = (Pred.mkPred₀ False ((Pred.nnf p1₃) ∧ (Pred.nnf p2₃)))) ->
       ((Pred.is_atom p1₃) -> (Pred.nnf p1₃)) ->
        ((Pred.is_atom p2₃) -> (Pred.nnf p2₃)) ->
         ((Pred.nnf p1₃)) ∧
         (∀ (v₃ : Pred),
          (Pred.nnf v₃) ->
           ((Pred.is_atom v₃) -> True) ->
            ((Pred.nnf p2₃)) ∧
            (∀ (v₄ : Pred),
             (Pred.nnf v₄) ->
              ((Pred.is_atom v₄) -> True) ->
               ((v₃ = (Pred.mkPred₀ True True)) ->
                ((k6 True True (Pred.is_atom v₀) True (Pred.is_atom p1₃) (Pred.nnf p1₃) (Pred.is_atom p2₃) (Pred.nnf p2₃) (Pred.is_atom v₃) True (Pred.is_atom v₄) True))) ∧
               ((v₃ = (Pred.mkPred₀ True True)) ->
                ((k6 (Pred.is_atom v₄) True (Pred.is_atom v₀) True (Pred.is_atom p1₃) (Pred.nnf p1₃) (Pred.is_atom p2₃) (Pred.nnf p2₃) (Pred.is_atom v₃) True (Pred.is_atom v₄) True))) ∧
               (((k7 (Pred.is_atom v₃) True (Pred.is_atom v₀) True (Pred.is_atom p1₃) (Pred.nnf p1₃) (Pred.is_atom p2₃) (Pred.nnf p2₃) (Pred.is_atom v₃) True (Pred.is_atom v₄) True))) ∧
               (∀ (a'₂₄ : Pred),
                ((k7 (Pred.is_atom a'₂₄) (Pred.nnf a'₂₄) (Pred.is_atom v₀) True (Pred.is_atom p1₃) (Pred.nnf p1₃) (Pred.is_atom p2₃) (Pred.nnf p2₃) (Pred.is_atom v₃) True (Pred.is_atom v₄) True)) ->
                 ((Pred.is_atom a'₂₄) -> (Pred.nnf a'₂₄)) ->
                  (((k8 (Pred.is_atom v₄) True (Pred.is_atom v₀) True (Pred.is_atom p1₃) (Pred.nnf p1₃) (Pred.is_atom p2₃) (Pred.nnf p2₃) (Pred.is_atom v₃) True (Pred.is_atom v₄) True (Pred.is_atom a'₂₄) (Pred.nnf a'₂₄)))) ∧
                  (∀ (a'₂₅ : Pred),
                   ((k8 (Pred.is_atom a'₂₅) (Pred.nnf a'₂₅) (Pred.is_atom v₀) True (Pred.is_atom p1₃) (Pred.nnf p1₃) (Pred.is_atom p2₃) (Pred.nnf p2₃) (Pred.is_atom v₃) True (Pred.is_atom v₄) True (Pred.is_atom a'₂₄) (Pred.nnf a'₂₄))) ->
                    ((Pred.is_atom a'₂₅) -> (Pred.nnf a'₂₅)) ->
                     ((k6 False ((Pred.nnf a'₂₄) ∧ (Pred.nnf a'₂₅)) (Pred.is_atom v₀) True (Pred.is_atom p1₃) (Pred.nnf p1₃) (Pred.is_atom p2₃) (Pred.nnf p2₃) (Pred.is_atom v₃) True (Pred.is_atom v₄) True)))
                  ) ∧
               (∀ (a'₂₆ : Pred),
                ((k6 (Pred.is_atom a'₂₆) (Pred.nnf a'₂₆) (Pred.is_atom v₀) True (Pred.is_atom p1₃) (Pred.nnf p1₃) (Pred.is_atom p2₃) (Pred.nnf p2₃) (Pred.is_atom v₃) True (Pred.is_atom v₄) True)) ->
                 ((k0 (Pred.is_atom a'₂₆) (Pred.nnf a'₂₆) (Pred.is_atom v₀) True)))
               )
            )
         ) ∧
    (∀ (a'₂₇ : Pred),
     ((k0 (Pred.is_atom a'₂₇) (Pred.nnf a'₂₇) (Pred.is_atom v₀) True)) ->
      (Pred.nnf a'₂₇))
    
end F
