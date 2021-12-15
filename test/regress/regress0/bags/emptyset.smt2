(set-logic ALL)
(set-info :status unsat)
(assert (>= (bag.count 5 (as bag.empty (Bag Int) )) 1))
(check-sat)
