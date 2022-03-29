; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun w () Real)

(assert (< x w))

(assert (> (exp x) (exp y)))
(assert (> (exp y) (exp z)))
(assert (> (exp z) (exp w)))


(check-sat)
