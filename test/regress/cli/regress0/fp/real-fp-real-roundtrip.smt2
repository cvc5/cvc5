; EXPECT: sat
; Satisfiable Real -> Float32 -> Real round trip where the rounding is not the
; identity: x must round to 5/8 while being strictly greater than 5/8, i.e. the
; model has to pick a non-representable x from the upper half of the rounding
; cell of 5/8. Exercises the refinement of both conversion abstractions
; (TheoryFp::refineAbstraction) on a sat answer, and the resulting model is
; checked by the default model tester (--debug-check-models).
(set-logic QF_FPLRA)
(declare-const x Real)
(define-fun rt ((v Real)) Real (fp.to_real ((_ to_fp 8 24) RNE v)))
(assert (= (rt x) (/ 5 8)))
(assert (> x (/ 5 8)))
(check-sat)
