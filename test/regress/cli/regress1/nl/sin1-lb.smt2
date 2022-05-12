; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)
(declare-fun x () Real)

(assert (> (sin 1) 0.842))
(assert (= x (sin 1)))

(check-sat)
