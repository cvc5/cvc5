; COMMAND-LINE: --learned-rewrite
; EXPECT: sat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 3))
(assert (<= x 5))
(assert (>= y 1))
(assert (<= y 2))
(assert (not (= (mod x y) x)))
(check-sat)
