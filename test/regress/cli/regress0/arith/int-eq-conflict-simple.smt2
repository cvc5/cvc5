; EXPECT: unsat
(set-logic QF_LIRA)
(declare-fun j () Int)
(assert (= 2.5 (to_real j)))
(check-sat)
