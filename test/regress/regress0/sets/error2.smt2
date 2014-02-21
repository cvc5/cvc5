(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)
(assert (= (as emptyset (Set Int)) (setenum 5)))
(check-sat)
