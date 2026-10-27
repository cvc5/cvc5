; EXPECT: unsat
(set-logic ALL)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (forall ((x Int)) (P x))))
(assert (not (P 100)))
(check-sat)
