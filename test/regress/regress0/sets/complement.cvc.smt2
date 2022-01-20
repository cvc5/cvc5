; EXPECT: sat
(set-option :incremental false)
(set-option :sets-ext true)
(set-logic ALL)
(declare-sort Atom 0)
(declare-fun a () (Set (Tuple Atom)))
(declare-fun b () (Set (Tuple Atom)))
(assert (= a (set.complement b)))
(check-sat)
