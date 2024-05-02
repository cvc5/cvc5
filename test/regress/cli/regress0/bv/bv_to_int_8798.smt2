; EXPECT: sat
(set-logic ALL)
(set-option :solve-bv-as-int iand)
(set-option :mbqi true)
(declare-sort byte 0)
(declare-fun to_rep1 (byte) (_ BitVec 8))
(assert (forall ((a (Array Int byte))) (exists ((temp Int)) (= (to_rep1 (select a temp)) (to_rep1 (select a (+ temp 1)))))))
(check-sat)
