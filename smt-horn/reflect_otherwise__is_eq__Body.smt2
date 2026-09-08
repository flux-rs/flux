(set-logic HORN)

;; Tag 0: Ret at 50:29: 50:33 (ESpan { span: tests/pos/enums/reflect_otherwise.rs:47:42: 47:50 (#0), base: None })
;; Tag 1: Ret at 51:29: 51:33 (ESpan { span: tests/pos/enums/reflect_otherwise.rs:47:42: 47:50 (#0), base: None })
;; Tag 2: Ret at 52:29: 52:33 (ESpan { span: tests/pos/enums/reflect_otherwise.rs:47:42: 47:50 (#0), base: None })
;; Tag 3: Ret at 53:14: 53:19 (ESpan { span: tests/pos/enums/reflect_otherwise.rs:47:42: 47:50 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0) (mkadt0$1) (mkadt0$2))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Adt0 Adt0) Bool)

(assert (forall ((reftgen$b1$0 Adt0)(reftgen$b2$1 Adt0)(_$ Int)(_$ Int)) (=> (and (= reftgen$b1$0 mkadt0$0) (= reftgen$b2$1 mkadt0$0) (not (= true (= reftgen$b1$0 reftgen$b2$1)))) false)))
(assert (forall ((reftgen$b1$0 Adt0)(reftgen$b2$1 Adt0)(_$ Int)(_$ Int)) (=> (and (= reftgen$b1$0 mkadt0$0) (or ((_ is mkadt0$1) reftgen$b2$1) ((_ is mkadt0$2) reftgen$b2$1))) (k0 reftgen$b1$0 reftgen$b2$1))))
(assert (forall ((reftgen$b1$0 Adt0)(reftgen$b2$1 Adt0)(_$ Int)(_$ Int)) (=> (and (= reftgen$b1$0 mkadt0$1) (= reftgen$b2$1 mkadt0$1) (not (= true (= reftgen$b1$0 reftgen$b2$1)))) false)))
(assert (forall ((reftgen$b1$0 Adt0)(reftgen$b2$1 Adt0)(_$ Int)(_$ Int)) (=> (and (= reftgen$b1$0 mkadt0$1) (or ((_ is mkadt0$0) reftgen$b2$1) ((_ is mkadt0$2) reftgen$b2$1))) (k0 reftgen$b1$0 reftgen$b2$1))))
(assert (forall ((reftgen$b1$0 Adt0)(reftgen$b2$1 Adt0)(_$ Int)(_$ Int)) (=> (and (= reftgen$b1$0 mkadt0$2) (= reftgen$b2$1 mkadt0$2) (not (= true (= reftgen$b1$0 reftgen$b2$1)))) false)))
(assert (forall ((reftgen$b1$0 Adt0)(reftgen$b2$1 Adt0)(_$ Int)(_$ Int)) (=> (and (= reftgen$b1$0 mkadt0$2) (or ((_ is mkadt0$0) reftgen$b2$1) ((_ is mkadt0$1) reftgen$b2$1))) (k0 reftgen$b1$0 reftgen$b2$1))))
(assert (forall ((reftgen$b1$0 Adt0)(reftgen$b2$1 Adt0)(_$ Int)) (=> (and (k0 reftgen$b1$0 reftgen$b2$1) (not (= false (= reftgen$b1$0 reftgen$b2$1)))) false)))

(check-sat)
