; COMMAND-LINE: --nl-ext=full --nl-ext-tplanes
; EXPECT: unsat
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)
(assert (or (< (sin 0.2) (- 0.1)) (> (sin (- 0.05)) 0.05))) 
(check-sat)
