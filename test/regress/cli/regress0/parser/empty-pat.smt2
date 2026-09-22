; EXPECT: unsat
(set-logic ALL)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (! (P x) :pattern ())))
(assert (not (P 0)))
(check-sat)
