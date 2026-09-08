(set-logic HORN)

;; Tag 0: Underflow at 19:32: 19:37
;; Tag 1: Call at 19:17: 19:38 (ESpan { span: tests/pos/surface/knuth_shuffle.rs:7:37: 7:44 (#0), base: None })
;; Tag 2: Underflow at 20:19: 20:24
;; Tag 3: Underflow at 20:19: 20:28
;; Tag 4: Call at 20:9: 20:29 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:71:47: 71:52 (#0), base: None })
;; Tag 5: Call at 20:9: 20:29 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:71:64: 71:69 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0)) (k0 0 (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (< a0 (fld0$0 reftgen$n$0)) (not (>= (- (fld0$0 reftgen$n$0) a0) 0))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (< a0 (fld0$0 reftgen$n$0)) (not (< 0 (- (fld0$0 reftgen$n$0) a0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (< a0 (fld0$0 reftgen$n$0)) (<= 0 a1) (< a1 (- (fld0$0 reftgen$n$0) a0)) (>= a1 0) (not (>= (- (fld0$0 reftgen$n$0) a0) 0))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (< a0 (fld0$0 reftgen$n$0)) (<= 0 a1) (< a1 (- (fld0$0 reftgen$n$0) a0)) (>= a1 0) (not (>= (- (- (fld0$0 reftgen$n$0) a0) 1) 0))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (< a0 (fld0$0 reftgen$n$0)) (<= 0 a1) (< a1 (- (fld0$0 reftgen$n$0) a0)) (>= a1 0) (not (< a1 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (< a0 (fld0$0 reftgen$n$0)) (<= 0 a1) (< a1 (- (fld0$0 reftgen$n$0) a0)) (>= a1 0) (not (< (- (- (fld0$0 reftgen$n$0) a0) 1) (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (< a0 (fld0$0 reftgen$n$0)) (<= 0 a1) (< a1 (- (fld0$0 reftgen$n$0) a0)) (>= a1 0)) (k0 (+ a0 1) (fld0$0 reftgen$n$0)))))

(check-sat)
