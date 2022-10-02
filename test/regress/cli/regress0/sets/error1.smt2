; EXPECT: sat
(set-logic QF_UFLIAFS)
(set-info :status sat)
(declare-fun A () (Set Int))
(declare-fun C () (Set Int))
(declare-fun D () (Set Int))
(declare-fun E () (Set Int))
(set-info :status sat)

(assert (= A (set.union D C)))
(assert (not (= A (set.union E A))))

(check-sat)
