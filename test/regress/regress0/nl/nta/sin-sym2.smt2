; COMMAND-LINE: --nl-ext --nl-ext-tplanes
; EXPECT: unsat
(set-logic QF_UFNRA)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (and (< 0.0 x) (< x 1.0) (< 0.0 y) (< y 1.0)))
(assert (= (+ (sin x) (sin y)) 0.0))
(assert (not (= (+ x y) 0.0)))
(check-sat)
