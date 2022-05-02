; COMMAND-LINE: --nl-ext=full --nl-ext-tplanes
; EXPECT: unsat
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)
(assert (or (> (sin 0.1) (sin 0.2)) (> (sin 6.4) (sin 6.5)))) 
(check-sat)
