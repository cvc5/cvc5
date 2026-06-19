(set-logic ALL)
(set-info :status sat)
(set-option :rels-exp true)

(assert (rel.acyclic (tuple (as set.empty (Relation Int Int)))))
(assert (rel.acyclic (tuple (set.singleton (tuple 0 1)))))
(check-sat)