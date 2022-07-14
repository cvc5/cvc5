; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Real)
(declare-fun f (Real) Real)
(assert (not (= (f 1.0) (f x))))
(assert (not (= (f 0.0) (f x))))
(assert (xor (= x 0.0) (= x 1.0)))
(check-sat)
