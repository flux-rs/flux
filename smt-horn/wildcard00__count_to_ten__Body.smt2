(set-logic HORN)

;; Tag 0: Ret at 16:5: 16:6 (ESpan { span: tests/pos/user_qualifiers/wildcard00.rs:10:27: 10:29 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (forall ((a0 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0) (not (< a0 10)) (not (= a0 10))) false)))
(assert (forall ((a0 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0) (< a0 10)) (k0 (+ a0 1)))))

(check-sat)
