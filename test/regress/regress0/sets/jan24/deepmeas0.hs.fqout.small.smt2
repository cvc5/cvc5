(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-fun x () Int)
(declare-fun y () Int)

(declare-fun S () (Set Int))
(declare-fun T () (Set Int))

(assert (in x S))

(assert (= S (union T (setenum y))))

(assert (not (= x y)))

(assert (not (in x T)))

(check-sat)
