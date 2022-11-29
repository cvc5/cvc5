; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun z () (Relation Int Int))
(assert (= y (rel.join (rel.tclosure x) x)))
(assert (not (= y (rel.tclosure x))))
(check-sat)
