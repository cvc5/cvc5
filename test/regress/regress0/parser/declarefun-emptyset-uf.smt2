; EXPECT: sat
(set-logic QF_UF)
(declare-sort T 0)
(declare-fun union () T)
(declare-fun emptyset () T)
(assert (= union emptyset))
(check-sat)
