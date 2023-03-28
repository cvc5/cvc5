; COMMAND-LINE: --learned-rewrite
; EXPECT: unsat
(set-logic QF_UFNIA)
(declare-fun i (Int Int Int) Int)
(assert (> 0 (i 0 0 0)))
(assert (= (i 0 0 0) (ite (= 0 (i 0 0 0)) 1 (mod 0 0))))
(check-sat)
