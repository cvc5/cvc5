; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(set-info :status sat)
(define-sort SetInt () (Set Int))

(declare-fun A () SetInt)
(declare-fun B () SetInt)
(declare-fun x () Int)
(assert (in x (union A B)))

(assert (not (in x (intersection A B))))
(assert (not (in x (setminus A B))))
;(assert (not (in x (setminus B A))))
;(assert (in x B))

(check-sat)
