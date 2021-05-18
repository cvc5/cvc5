; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)
(assert (not (= (cos 0.0) 1.0)))
(check-sat)
