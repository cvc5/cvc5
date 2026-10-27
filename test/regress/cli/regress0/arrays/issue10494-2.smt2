; EXPECT: sat
(set-logic ALL)
(declare-const a (Array Int (_ BitVec 1)))
(assert (= a (store a 0 (bvadd #b1 (select a 1)))))
(check-sat)
