; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun i () Int)
(assert (= (+ 1 (- i x)) ((_ iand 2) 1 i)))
(assert (< x 4))
(assert (= 0 ((_ iand 2) 1 x)))
(check-sat)
