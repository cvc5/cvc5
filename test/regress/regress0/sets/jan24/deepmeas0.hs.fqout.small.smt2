(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-fun x () Int)
(declare-fun y () Int)

(declare-fun S () (Set Int))
(declare-fun T () (Set Int))

(assert (member x S))

(assert (= S (union T (singleton y))))

(assert (not (= x y)))

(assert (not (member x T)))

(check-sat)
