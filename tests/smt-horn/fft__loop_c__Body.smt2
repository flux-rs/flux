(set-logic HORN)

;; Tag 0: Underflow at 122:13: 122:25
;; Tag 1: Call at 128:24: 128:27 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:181:44: 181:49 (#0), base: None })
;; Tag 2: Call at 129:23: 129:26 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:181:44: 181:49 (#0), base: None })
;; Tag 3: Call at 129:15: 129:18 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:189:48: 189:53 (#0), base: None })
;; Tag 4: Call at 130:15: 130:18 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:189:48: 189:53 (#0), base: None })
;; Tag 5: Call at 132:24: 132:27 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:181:44: 181:49 (#0), base: None })
;; Tag 6: Call at 133:23: 133:26 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:181:44: 181:49 (#0), base: None })
;; Tag 7: Call at 133:15: 133:18 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:189:48: 189:53 (#0), base: None })
;; Tag 8: Call at 134:15: 134:18 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:189:48: 189:53 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k1
(declare-fun k0 (Int Int Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int) Bool)
;; orig: $k0
(declare-fun k2 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (>= (- (fld0$0 reftgen$n$0) 1) 0))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0)) (k0 1 1 (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0)) (k1 1 (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (not (< a0 a1))) (k2 (fld0$0 reftgen$n$0) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (< a0 a1) (not (< a1 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (< a0 a1) (not (< a0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (< a0 a1) (not (< a1 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (< a0 a1) (not (< a0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (< a0 a1) (not (< a1 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (< a0 a1) (not (< a0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (< a0 a1) (not (< a1 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (< a0 a1) (not (< a0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (< a0 a1)) (k2 (fld0$0 reftgen$n$0) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (k2 (fld0$0 reftgen$n$0) a0 a1) (<= a2 (+ (div (- (fld0$0 reftgen$n$0) 1) 2) (div (- (fld0$0 reftgen$n$0) 1) 2))) (>= a2 0)) (k0 (+ a0 1) a2 (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (<= 2 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 a1 (fld0$0 reftgen$n$0)) (k1 a1 (fld0$0 reftgen$n$0)) (< a0 (- (fld0$0 reftgen$n$0) 1)) (k2 (fld0$0 reftgen$n$0) a0 a1) (<= a2 (+ (div (- (fld0$0 reftgen$n$0) 1) 2) (div (- (fld0$0 reftgen$n$0) 1) 2))) (>= a2 0)) (k1 a2 (fld0$0 reftgen$n$0)))))

(check-sat)
