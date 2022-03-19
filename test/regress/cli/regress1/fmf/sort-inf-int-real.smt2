; COMMAND-LINE: --finite-model-find --sort-inference
; EXPECT: sat
(set-logic UFLIRA)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-fun g (Int) Real)
(declare-fun h (Real) Int)
(assert (forall ((x Int)) (or (= (f x) (h (to_real x))) (= (f x) (to_int (g x))))))
(assert (not (= (f 3) (h 3.0))))
(assert (not (= (f 5) (to_int (g 5)))))
(assert (= (f 4) (g 8)))
(assert (= (h 5.0) 0.0))
; Sort inference fails to infer that x can be uninterpreted in this example,
; however, fmf is able to reason that all instances are sat.
(check-sat)
