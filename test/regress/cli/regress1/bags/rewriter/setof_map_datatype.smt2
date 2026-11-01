; REQUIRES: unrestricted-mode
; SETOF_PROJECTION_SORT reads a map as a projection onto columns only when
; its rows are tuples: the map below reads the fields of a datatype in
; another order, (tuple (field1 x) (field0 x)), and is no projection
(set-logic HO_ALL)
(set-info :status sat)
(declare-datatype D ((mk (field0 Int) (field1 Int))))
(declare-const X (Bag D))
(define-fun swap ((x D)) (Tuple Int Int) (tuple (field1 x) (field0 x)))
(assert (= (bag.setof (bag.map swap X)) (bag (tuple 1 2) 1)))
(check-sat)
