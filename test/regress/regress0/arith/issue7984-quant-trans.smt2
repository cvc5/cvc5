; COMMAND-LINE: -q
; EXPECT: sat
(set-logic QF_NRAT)
(set-option :re-elim-agg true)
(declare-fun r6 () Real)
(assert (= 0.0 (cos r6)))
(check-sat)
