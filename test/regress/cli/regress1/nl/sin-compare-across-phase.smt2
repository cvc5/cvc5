; COMMAND-LINE: --nl-ext=full --nl-ext-tplanes
; EXPECT: unsat
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)
(assert (< (sin 3.1) (sin 3.3)))
(check-sat)
