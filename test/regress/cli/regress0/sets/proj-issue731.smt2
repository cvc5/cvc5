; EXPECT: unsat
(set-logic ALL)
(set-option :sets-exp true)
(set-option :debug-check-models true)
(declare-sort _u0 0)
(declare-const _x3 _u0)
(assert (set.subset (set.singleton _x3) (set.complement (set.singleton _x3))))
(check-sat)
