; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(define-sort SetInt () (Set Int))

(declare-fun A () SetInt)
(declare-fun B () SetInt)
(declare-fun x () Int)
(assert (set.member x (set.union A B)))

(assert (not (set.member x (set.inter A B))))
(assert (not (set.member x (set.minus A B))))
;(assert (not (set.member x (set.minus B A))))
;(assert (set.member x B))

(check-sat)
