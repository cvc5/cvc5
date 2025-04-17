; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 8))
(assert (not (= 
(concat ((_ extract 7 7) x) ((_ extract 5 5) x) ((_ extract 4 4) x) ((_ extract 3 3) x)) 
(concat ((_ extract 7 7) x) ((_ extract 5 3) x)))))
(check-sat)
