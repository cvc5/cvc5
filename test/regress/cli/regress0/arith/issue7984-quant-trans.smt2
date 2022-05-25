; EXPECT: sat
(set-logic QF_NRAT)
(set-info :status sat)
(set-option :re-elim agg)
(declare-fun r6 () Real)
(assert (= 0.0 (cos r6)))
(check-sat)
