(set-logic HORN)

;; Tag 0: Underflow at 21:9: 21:17
;; Tag 1: Call at 22:9: 22:25 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:71:47: 71:52 (#0), base: None })
;; Tag 2: Call at 22:9: 22:25 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:71:64: 71:69 (#0), base: None })
;; Tag 3: Underflow at 23:28: 23:35
;; Tag 4: Call at 23:9: 23:36 (ESpan { span: tests/pos/surface/heapsort.rs:28:48: 28:55 (#0), base: None })
;; Tag 5: Call at 23:9: 23:36 (ESpan { span: tests/pos/surface/heapsort.rs:28:68: 28:75 (#0), base: None })
;; Tag 6: Underflow at 15:9: 15:19
;; Tag 7: Underflow at 16:32: 16:39
;; Tag 8: Call at 16:9: 16:40 (ESpan { span: tests/pos/surface/heapsort.rs:28:48: 28:55 (#0), base: None })
;; Tag 9: Call at 16:9: 16:40 (ESpan { span: tests/pos/surface/heapsort.rs:28:68: 28:75 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0))) (k0 (div (fld0$0 reftgen$n$0) 2) (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (not (> a0 0))) (k1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$n$0) a0))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (not (> a0 0)) (k1 a1 (fld0$0 reftgen$n$0) a0) (> a1 1) (not (>= (- a1 1) 0))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (not (> a0 0)) (k1 a1 (fld0$0 reftgen$n$0) a0) (> a1 1) (not (< 0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (not (> a0 0)) (k1 a1 (fld0$0 reftgen$n$0) a0) (> a1 1) (not (< (- a1 1) (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (not (> a0 0)) (k1 a1 (fld0$0 reftgen$n$0) a0) (> a1 1) (not (>= (- (- a1 1) 1) 0))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (not (> a0 0)) (k1 a1 (fld0$0 reftgen$n$0) a0) (> a1 1) (not (< 0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (not (> a0 0)) (k1 a1 (fld0$0 reftgen$n$0) a0) (> a1 1) (not (< (- (- a1 1) 1) (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(a2 Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (not (> a0 0)) (k1 a1 (fld0$0 reftgen$n$0) a0) (> a1 1)) (k1 (- a1 1) (fld0$0 reftgen$n$0) a0))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (> a0 0) (not (>= (- a0 1) 0))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (> a0 0) (not (>= (- (fld0$0 reftgen$n$0) 1) 0))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (> a0 0) (not (< (- a0 1) (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (> a0 0) (not (< (- (fld0$0 reftgen$n$0) 1) (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a3 Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (<= (fld0$0 reftgen$n$0) 0)) (k0 a0 (fld0$0 reftgen$n$0)) (> a0 0)) (k0 (- a0 1) (fld0$0 reftgen$n$0)))))

(check-sat)
