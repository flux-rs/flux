(set-logic HORN)

;; Tag 0: Ret at 91:5: 91:6 (ESpan { span: tests/pos/surface/rset01.rs:84:33: 84:39 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (=> true (k0 666)))
(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0))))
(assert (=> true (k1 667)))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (k1 a1) (not (<= 666 a1))) false)))

(check-sat)
