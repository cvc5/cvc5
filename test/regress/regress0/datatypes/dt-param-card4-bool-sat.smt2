(set-logic QF_ALL_SUPPORTED)
(set-info :status sat)
(declare-datatypes (T S) ( (Pair (pair (first T) (second S)) ) ) )

(declare-fun p1 () (Pair Bool Bool))
(declare-fun p2 () (Pair Bool Bool))
(declare-fun p3 () (Pair Bool Bool))
(declare-fun p4 () (Pair Bool Bool))

(assert (distinct p1 p2 p3 p4))
(check-sat)
