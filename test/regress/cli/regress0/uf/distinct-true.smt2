; EXPECT: unsat
(set-logic QF_UFLIA)
(assert (not (distinct 0 1 2 3 4 5)))
(check-sat)
