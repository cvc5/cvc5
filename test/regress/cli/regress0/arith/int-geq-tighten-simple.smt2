; EXPECT: unsat
(set-logic ALL)
(declare-fun i () Int)
(assert (>= (to_real i) 2.5))
(assert (= i 0))
(check-sat)
