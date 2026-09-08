(set-logic HORN)

;; Tag 0: Ret at 20:28: 20:37 (ESpan { span: tests/with_deps/pos/surface/static_spec01.rs:19:25: 19:30 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (=> true (k0 1)))
(assert (=> true (k0 2)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (< a0 5))) false)))

(check-sat)
