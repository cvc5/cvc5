(set-logic ALL)
(set-info :status unsat)
(set-option :rels-exp true)

(assert (rel.acyclic (set.union (set.singleton (tuple 1 0)) (set.singleton (tuple 0 1)))))
(check-sat)