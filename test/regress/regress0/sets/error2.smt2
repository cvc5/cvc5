(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)
(assert (= (as emptyset (Set Int)) (singleton 5)))
(check-sat)
