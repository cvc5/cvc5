(set-logic QF_ALL)
(set-info :status unsat)
(assert (= (as bag.empty (Bag Int)) (bag 5 1)))
(check-sat)
