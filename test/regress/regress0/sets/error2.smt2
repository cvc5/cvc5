(set-logic QF_ALL)
(set-info :status unsat)
(assert (= (as emptyset (Set Int)) (singleton 5)))
(check-sat)
