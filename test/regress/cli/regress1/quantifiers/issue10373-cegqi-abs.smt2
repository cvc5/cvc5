; EXPECT: unsat
(set-logic LIA)
(assert (forall ((t Int)) (= 0 (abs t))))
(check-sat)
