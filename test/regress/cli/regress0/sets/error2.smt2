(set-logic QF_ALL)
(set-info :status unsat)
(assert (= (as set.empty (Set Int)) (set.singleton 5)))
(check-sat)
