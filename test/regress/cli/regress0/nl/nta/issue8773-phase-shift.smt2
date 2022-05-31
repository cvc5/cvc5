; EXPECT: unsat
(set-logic QF_NRAT)
(assert (= 0.0 (sin 7)))
(check-sat)
