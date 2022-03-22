; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)


(assert (= (tan x) (sin x)))
(assert (> (cos x) 0))
(assert (not (= (cos x) 1)))
(assert (not (= (sin x) 0)))

(check-sat)
