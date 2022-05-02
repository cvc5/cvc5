; EXPECT: sat
(set-option :incremental false)
(set-option :sets-ext true)
(set-logic ALL)
(declare-sort Atom 0)
(declare-fun a () (Relation Atom))
(declare-fun b () (Relation Atom))
(assert (= a (set.complement b)))
(check-sat)
