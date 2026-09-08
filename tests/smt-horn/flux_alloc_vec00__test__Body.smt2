(set-logic HORN)

;; Tag 0: Call at 9:17: 9:20 (ESpan { span: lib/flux-core/src/slice/index.rs:48:58: 48:67 (#0), base: None })
;; Tag 1: Call at 9:9: 9:25 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k2
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a0)) (>= (fld0$0 a0) 0) (> (fld0$0 a0) 0) (> a1 0)) (k0 a1 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a0)) (>= (fld0$0 a0) 0) (> (fld0$0 a0) 0) (not (< 0 (fld0$0 a0)))) false)))
(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a0)) (>= (fld0$0 a0) 0) (> (fld0$0 a0) 0) (k0 a2 (fld0$0 a0)) (not (= (> a2 0) true))) false)))

(check-sat)
