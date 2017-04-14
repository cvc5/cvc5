(set-logic ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun C () (Set Int))
(declare-fun D () (Set Int))

(assert (member x A))
(assert (member y B))
(assert (or (= C (intersection A B)) (= D (intersection A B))))


(check-sat)
