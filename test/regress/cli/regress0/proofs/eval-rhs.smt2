; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 32))
(assert (not (= ((_ extract 3 1) ((_ extract 7 1) x)) ((_ extract 4 2) x))))
(check-sat)
