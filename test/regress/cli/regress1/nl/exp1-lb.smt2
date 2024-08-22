; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)
(declare-fun x () Real)

(assert (> (exp 1) 2.719))
(assert (= x (exp 1)))

(check-sat)
