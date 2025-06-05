; EXPECT: unsat
(set-logic ALL)
(declare-fun d () Int)
(assert (forall ((v Int)) (or (= d (div v 2)) (= 0 (mod (div v 2) 2)))))
(check-sat)
