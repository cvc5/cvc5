; EXPECT: sat
(set-logic QF_UFBVFS)
(set-info :status sat)
(declare-fun x () (Set (_ BitVec 2)))
(declare-fun y () (Set (_ BitVec 2)))
(assert (not (= x y)))
(check-sat)
