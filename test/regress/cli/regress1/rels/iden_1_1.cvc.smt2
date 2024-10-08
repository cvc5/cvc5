; EXPECT: sat
(set-option :incremental false)
(set-option :sets-exp true)
(set-logic ALL)
(declare-sort Atom 0)

(declare-fun x () (Relation Atom Atom))
(declare-fun t () (Relation Atom))
(declare-fun univ () (Relation Atom))
(declare-fun univ2 () (Relation Atom Atom))
(declare-fun a () Atom)
(declare-fun b () Atom)
(declare-fun c () Atom)
(declare-fun d () Atom)
(assert (= univ (as set.universe (Relation Atom))))
(assert (= univ2 (as set.universe (Relation Atom Atom))))
(assert (= univ2 (rel.product univ univ)))
(assert (set.member (tuple a b) x))
(assert (set.member (tuple c d) x))
(assert (not (= a b)))
(assert (set.subset (rel.iden univ) x))
(check-sat)
