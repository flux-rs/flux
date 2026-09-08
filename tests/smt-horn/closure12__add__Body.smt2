(set-logic HORN)

;; Tag 0: Call at 80:5: 80:31 (ESpan { span: tests/with_deps/pos/surface/closure12.rs:10:17: 10:21 (#0), base: None })
;; Tag 1: Call at 81:34: 81:37 (ESpan { span: lib/flux-core/src/slice/index.rs:48:58: 48:67 (#0), base: None })
;; Tag 2: Call at 81:41: 81:44 (ESpan { span: lib/flux-core/src/slice/index.rs:48:58: 48:67 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k3
(declare-fun k0 (Int Int) Bool)
;; orig: $k5
(declare-fun k1 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (not (= (= (fld0$0 reftgen$n$0) (fld0$0 reftgen$n$0)) true))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (>= a0 0)) (k1 a1 (fld0$0 reftgen$n$0) a0))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (>= a0 0) (not (< a0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a0 (fld0$0 reftgen$n$0)) (>= a0 0) (k1 a2 (fld0$0 reftgen$n$0) a0) (not (< a0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (<= 0 a3) (< a3 (fld0$0 reftgen$n$0))) (k0 a3 (fld0$0 reftgen$n$0)))))

(check-sat)
