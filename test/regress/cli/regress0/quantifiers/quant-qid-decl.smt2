; EXPECT: unsat
(set-logic LIA)
(declare-fun id1 () Int)
(assert (forall ((x Int)) (! (> x 0) :qid id1)))
(check-sat)
