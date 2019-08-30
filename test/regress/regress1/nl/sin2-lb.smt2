; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)
(declare-fun x () Real)

(assert (> (sin 2) 0.96))
(assert (= x (sin 2)))

(check-sat)
