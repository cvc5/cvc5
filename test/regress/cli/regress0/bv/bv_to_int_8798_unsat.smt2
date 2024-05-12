; EXPECT: unsat
(set-logic ALL)
(set-option :mbqi true)
(set-option :solve-bv-as-int iand)
(declare-sort byte 0)
(declare-fun to_rep1 (byte) (_ BitVec 1))
(assert (forall ((a (Array Int byte))) (exists ((temp Int)) (distinct (to_rep1 (select a temp)) (to_rep1 (select a (+ temp 1))) (to_rep1 (select a (+ temp 2)))  ))))

(check-sat)
