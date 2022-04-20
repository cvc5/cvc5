; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(assert (= y (rel.tclosure x)))
(assert (not (set.subset (rel.join (rel.join x x) x) y)))
(check-sat)
