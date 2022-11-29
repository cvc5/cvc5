; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(assert (= y (rel.tclosure x)))
(assert (not (= y (rel.join (rel.join x x) x))))
(check-sat)
