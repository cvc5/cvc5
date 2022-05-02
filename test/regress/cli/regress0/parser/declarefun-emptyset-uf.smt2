; EXPECT: sat
(set-logic QF_UF)
(declare-sort T 0)
(declare-fun union () T)
(declare-fun set.empty () T)
(assert (= union set.empty))
(check-sat)
