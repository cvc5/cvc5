; EXPECT: unsat
(set-logic QF_BV)
(set-info :status unsat)

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun c () (_ BitVec 1))
(assert (not (= (bvite c (bvite c y x) y) (bvite c y (bvite c x y)))))
(check-sat)
(exit)
