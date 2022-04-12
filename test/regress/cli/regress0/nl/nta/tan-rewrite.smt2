; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)

(assert (= (sin x) 0.24))
(assert (= (cos x) 0.4))
(assert (= (tan x) 0.5))

(check-sat)
