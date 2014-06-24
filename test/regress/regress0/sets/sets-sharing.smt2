(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-fun S () (Set Int))
(declare-fun x () Int)

(assert (member (+ 5 x) S))
(assert (not (member 9 S)))
(assert (= x 4))

(check-sat)
