; EXPECT: unknown
(set-option :incremental false)
(set-logic ALL)

(declare-fun x () (Relation Int Int))
(assert (> (set.card (rel.transpose x)) 0))
(check-sat)
