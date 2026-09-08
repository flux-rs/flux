(set-logic HORN)

;; Tag 0: Ret at 108:5: 108:87 (ESpan { span: tests/with_deps/pos/surface/bv_ord.rs:99:5: 105:34 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 (_ BitVec 32))))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 ((_ BitVec 32) (_ BitVec 32)) Bool)

(assert (forall ((reftgen$x$0 Adt0)(reftgen$y$1 Adt0)(_$ Int)) (=> (not (bvule (fld0$0 reftgen$x$0) ((_ int2bv 32) 10))) (k0 (fld0$0 reftgen$x$0) (fld0$0 reftgen$y$1)))))
(assert (forall ((reftgen$x$0 Adt0)(reftgen$y$1 Adt0)(_$ Int)(_$ Int)) (=> (and (bvule (fld0$0 reftgen$x$0) ((_ int2bv 32) 10)) (not (bvuge (fld0$0 reftgen$y$1) ((_ int2bv 32) 20)))) (k0 (fld0$0 reftgen$x$0) (fld0$0 reftgen$y$1)))))
(assert (forall ((reftgen$x$0 Adt0)(reftgen$y$1 Adt0)(_$ Int)(_$ Int)(_$ Int)) (=> (and (bvule (fld0$0 reftgen$x$0) ((_ int2bv 32) 10)) (bvuge (fld0$0 reftgen$y$1) ((_ int2bv 32) 20)) (not (bvult (fld0$0 reftgen$x$0) ((_ int2bv 32) 11)))) (k0 (fld0$0 reftgen$x$0) (fld0$0 reftgen$y$1)))))
(assert (forall ((reftgen$x$0 Adt0)(reftgen$y$1 Adt0)(_$ Int)) (=> (and (k0 (fld0$0 reftgen$x$0) (fld0$0 reftgen$y$1)) (not (= false (and (and (and (bvule (fld0$0 reftgen$x$0) ((_ int2bv 32) 10)) (bvuge (fld0$0 reftgen$y$1) ((_ int2bv 32) 20))) (bvult (fld0$0 reftgen$x$0) ((_ int2bv 32) 11))) (bvugt (fld0$0 reftgen$y$1) ((_ int2bv 32) 21)))))) false)))

(check-sat)
