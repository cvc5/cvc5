(set-logic ALL)
(set-info :status unsat)

(declare-fun x () Int)
(declare-fun y () Int)

(declare-fun S () (Set Int))
(declare-fun T () (Set Int))

(assert (set.member x S))

(assert (= S (set.union T (set.singleton y))))

(assert (not (= x y)))

(assert (not (set.member x T)))

(check-sat)
