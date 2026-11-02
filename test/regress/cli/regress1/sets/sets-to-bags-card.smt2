; COMMAND-LINE: --sets-to-bags=setof --fmf-bound
; EXPECT: sat
(set-logic QF_UFLIAFS)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(assert (= (set.card A) 2))
(assert (set.subset A B))
(assert (= (set.card B) 3))
(check-sat)
