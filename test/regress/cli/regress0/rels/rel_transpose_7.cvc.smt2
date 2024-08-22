; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(assert (= x y))
(assert (not (= (rel.transpose x) (rel.transpose y))))
(check-sat)
