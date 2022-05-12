; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)
(declare-fun a6 () Bool)
(assert (= a6 (> (* (csc 1.0) (sin 1.0)) 1.0)))
(assert a6)
(check-sat)
