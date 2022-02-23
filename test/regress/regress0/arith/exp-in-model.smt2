; COMMAND-LINE: -q
; EXPECT: sat
(set-logic QF_UFNRAT)
(set-info :status sat)
(declare-fun b (Real) Real)
(declare-fun v () Real)
(assert (distinct 0 (* v v)))
(assert (= 0.0 (b (exp 1.0))))
(check-sat)
