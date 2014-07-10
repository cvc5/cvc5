; EXPECT: sat
(set-logic QF_UFLIAFS)
(set-info :status sat)
(declare-fun A () (Set Int))
(declare-fun C () (Set Int))
(declare-fun D () (Set Int))
(declare-fun E () (Set Int))
(set-info :status sat)

(assert (= A (union D C)))
(assert (not (= A (union E A))))

(check-sat)
