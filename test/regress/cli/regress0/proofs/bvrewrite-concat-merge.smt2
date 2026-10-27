; EXPECT: unsat
(set-logic QF_BV)
(set-info :status unsat)

(declare-fun x1 () (_ BitVec 1))
(declare-fun x2 () (_ BitVec 1))
(declare-fun x3 () (_ BitVec 1))
(declare-fun x4 () (_ BitVec 1))
(assert (not (= (concat x1 x2 x3 x4) (concat (concat x1 x2) (concat x3 x4)))))
(check-sat)
(exit)
