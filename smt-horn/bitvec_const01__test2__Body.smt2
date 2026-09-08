(set-logic HORN)

;; Tag 0: Ret at 36:16: 36:21 (ESpan { span: tests/with_deps/pos/surface/bitvec_const01.rs:34:41: 34:54 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 (_ BitVec 32))))))
(define-fun c0 () Adt0 (mkadt0$0 ((_ int2bv 32) 17767)))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 ((_ BitVec 32) (_ BitVec 32)) Bool)

(assert (forall ((_$ Int)(reftgen$addr$0 Adt0)(a0 Int)) (=> (and (= c0 (mkadt0$0 ((_ int2bv 32) 17767))) (= a0 0)) (k0 a0))))
(assert (forall ((_$ Int)(reftgen$addr$0 Adt0)) (=> (= c0 (mkadt0$0 ((_ int2bv 32) 17767))) (k1 ((_ int2bv 32) 17767) (fld0$0 reftgen$addr$0)))))
(assert (forall ((_$ Int)(reftgen$addr$0 Adt0)(a1 Int)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (= c0 (mkadt0$0 ((_ int2bv 32) 17767))) (= a1 0) (k0 a1) (k1 (fld0$0 a2) (fld0$0 reftgen$addr$0)) (not (= (= reftgen$addr$0 a2) (= reftgen$addr$0 c0)))) false)))

(check-sat)
