(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun C () (Set Int))
(declare-fun D () (Set Int))

(assert (set.member x A))
(assert (set.member y B))
(assert (or (= C (set.inter A B)) (= D (set.inter A B))))


(check-sat)
