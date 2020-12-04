; EXPECT: sat
(set-logic UFC)
(declare-sort a 0)
(declare-fun b () a)
(assert (not (fmf.card b 1)))
(check-sat)