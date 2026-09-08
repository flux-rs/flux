(set-logic HORN)

;; Tag 0: Call at 217:9: 217:21 (ESpan { span: tests/pos/surface/fft.rs:161:26: 161:32 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (=> true (k0 4 16)))
(assert (=> true (k1 16)))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1) (k1 a1) (<= a0 16) (not (>= a1 2))) false)))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1) (k1 a1) (<= a0 16)) (k0 (+ a0 1) (* a1 2)))))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1) (k1 a1) (<= a0 16)) (k1 (* a1 2)))))

(check-sat)
