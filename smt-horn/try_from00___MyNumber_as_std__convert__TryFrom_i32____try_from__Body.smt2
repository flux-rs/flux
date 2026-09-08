(set-logic HORN)

;; Tag 0: Ret at 17:9: 17:36 (ESpan { span: tests/with_deps/pos/surface/try_from00.rs:15:46: 15:56 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$x$0 Int)) (=> true (k0 reftgen$x$0 reftgen$x$0))))
(assert (forall ((reftgen$x$0 Int)(a0 Adt0)(_$ Int)) (=> (and (k0 (fld0$0 a0) reftgen$x$0) (not (= reftgen$x$0 (fld0$0 a0)))) false)))

(check-sat)
