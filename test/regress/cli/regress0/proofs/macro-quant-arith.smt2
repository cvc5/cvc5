; REQUIRES: unrestricted-mode
; DISABLE-TESTER: alethe
; COMMAND-LINE: --macros-quant --macros-quant-mode=ground --proof-granularity=dsl-rewrite --proof-check=eager
; EXPECT: unsat
(set-logic UFLRA)
(declare-fun f (Real Real) Real)
; Solving requires scaling, and the arguments differ from the binder order.
(assert (forall ((x Real) (y Real))
  (! (= (+ (* 3 (f y x)) x) y) :pattern ((f y x)))))
(assert (not (= (f 6 3) 1)))
(check-sat)
