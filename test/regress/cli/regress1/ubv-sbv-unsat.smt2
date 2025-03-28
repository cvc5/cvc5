; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 8))
(assert (not (= (ubv_to_int x) (sbv_to_int x))))
(assert (bvsgt x #b00000000))
(check-sat)
