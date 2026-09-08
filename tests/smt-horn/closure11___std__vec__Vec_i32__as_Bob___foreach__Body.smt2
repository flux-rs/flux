(set-logic HORN)

;; Tag 0: NoPanic(DefId(2:4248 ~ core[9471]::ops::function::FnMut::call_mut), MightPanic(NotInCallGraph)) at 24:38: 24:42

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
;; alias reft: <({b0. F[b0] | $k5(b0) }) as FnOnce<({b1. usize[b1] | $k6(b1) },)>>::no_panic
(declare-const c0 Bool)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k3
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (k0 a1 (fld0$0 reftgen$n$0) a0) (>= a1 0) (not (=> false (or c0 false)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= (fld0$0 reftgen$n$0) 0) (<= 0 a2) (< a2 (fld0$0 reftgen$n$0))) (k0 a2 (fld0$0 reftgen$n$0) a0))))

(check-sat)
