; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(declare-fun y () (Relation Int Int))
(declare-fun z () (Relation Int Int))
(assert (or (= z (rel.transpose y)) (= z (rel.transpose x))))
(assert (not (= (rel.transpose z) y)))
(assert (not (= (rel.transpose z) x)))
(check-sat)
