; EXPECT: sat
(set-logic ALL_SUPPORTED)
(set-info :status sat)
(define-sort SetInt () (Set Int))

(declare-fun A () SetInt)
(declare-fun B () SetInt)
(declare-fun x () Int)
(assert (member x (union A B)))

(assert (not (member x (intersection A B))))
(assert (not (member x (setminus A B))))
;(assert (not (member x (setminus B A))))
;(assert (member x B))

(check-sat)
