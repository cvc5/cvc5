; EXPECT: unsat
(set-logic ALL)
(declare-const x (Tuple Int Bool))
(assert (not (= x ((_ tuple.update 1) x true))))
(assert (not (= x ((_ tuple.update 1) x false))))
(check-sat)
