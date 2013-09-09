; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(set-info :status sat)
(define-sort SetInt () (Set Int))
(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (in x (union A B)))
(assert (not (in y A)))
(assert (not (in y B)))
(check-sat)
