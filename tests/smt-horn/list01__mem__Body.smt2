(set-logic HORN)

;; Tag 0: Ret at 74:1: 74:2 (ESpan { span: tests/pos/enums/list01.rs:62:42: 62:64 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 (Set Int))))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Bool Int (Set Int)) Bool)
;; orig: $k1
(declare-fun k1 (Bool Int (Set Int) Int (Set Int)) Bool)

(assert (forall ((reftgen$k$0 Int)(reftgen$xs$1 Adt0)(_$ Int)) (=> (= reftgen$xs$1 (mkadt0$0 ((as const (Set Int)) false))) (k0 false reftgen$k$0 (fld0$0 reftgen$xs$1)))))
(assert (forall ((reftgen$k$0 Int)(reftgen$xs$1 Adt0)(a0 Int)(a1 Adt0)(_$ Int)(_$ Int)) (=> (and (= reftgen$xs$1 (mkadt0$0 (union (store ((as const (Set Int)) false) a0 true) (fld0$0 a1)))) (not (= reftgen$k$0 a0))) (k1 (select (fld0$0 a1) reftgen$k$0) reftgen$k$0 (fld0$0 reftgen$xs$1) a0 (fld0$0 a1)))))
(assert (forall ((reftgen$k$0 Int)(reftgen$xs$1 Adt0)(a0 Int)(a1 Adt0)(_$ Int)(_$ Int)) (=> (and (= reftgen$xs$1 (mkadt0$0 (union (store ((as const (Set Int)) false) a0 true) (fld0$0 a1)))) (not (not (= reftgen$k$0 a0)))) (k1 true reftgen$k$0 (fld0$0 reftgen$xs$1) a0 (fld0$0 a1)))))
(assert (forall ((reftgen$k$0 Int)(reftgen$xs$1 Adt0)(a0 Int)(a1 Adt0)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (= reftgen$xs$1 (mkadt0$0 (union (store ((as const (Set Int)) false) a0 true) (fld0$0 a1)))) (k1 a2 reftgen$k$0 (fld0$0 reftgen$xs$1) a0 (fld0$0 a1))) (k0 a2 reftgen$k$0 (fld0$0 reftgen$xs$1)))))
(assert (forall ((reftgen$k$0 Int)(reftgen$xs$1 Adt0)(a3 Bool)(_$ Int)) (=> (and (k0 a3 reftgen$k$0 (fld0$0 reftgen$xs$1)) (not (= a3 (select (fld0$0 reftgen$xs$1) reftgen$k$0)))) false)))

(check-sat)
