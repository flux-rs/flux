(set-logic HORN)

;; Tag 0: Call at 14:5: 14:32 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 1: Call at 16:5: 16:32 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (forall ((a0 Int)) (=> (= a0 0) (k0 a0))))
(assert (forall ((a1 Int)) (=> (= a1 0) (k1 a1))))
(assert (forall ((a2 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Adt0)(_$ Int)(_$ Int)) (=> (and (= a2 0) (k0 a2) (= a3 0) (k1 a3) (= (fld0$0 a4) (ite (> (ite (> 0 (- (- 0 0) 0)) 0 (- (- 0 0) 0)) 0) (- (ite (> 0 (- (- 0 0) 0)) 0 (- (- 0 0) 0)) 1) (ite (> 0 (- (- 0 0) 0)) 0 (- (- 0 0) 0)))) (>= (fld0$0 a4) 0) (not (= (= (fld0$0 a4) 0) true))) false)))
(assert (forall ((a2 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Adt0)(_$ Int)(_$ Int)(a5 Adt0)(_$ Int)(_$ Int)) (=> (and (= a2 0) (k0 a2) (= a3 0) (k1 a3) (= (fld0$0 a4) (ite (> (ite (> 0 (- (- 0 0) 0)) 0 (- (- 0 0) 0)) 0) (- (ite (> 0 (- (- 0 0) 0)) 0 (- (- 0 0) 0)) 1) (ite (> 0 (- (- 0 0) 0)) 0 (- (- 0 0) 0)))) (>= (fld0$0 a4) 0) (= (fld0$0 a5) (ite (> (fld0$0 a4) 0) (- (fld0$0 a4) 1) (fld0$0 a4))) (>= (fld0$0 a5) 0) (not (= (= (fld0$0 a5) 0) true))) false)))

(check-sat)
