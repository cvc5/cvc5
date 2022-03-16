; COMMAND-LINE: --sygus-inference
; EXPECT: sat
(set-logic ALL)
(declare-sort S 1)
(define-sort SB () (S Bool))
(declare-fun A () (S Bool))
(declare-fun B () SB)
(assert (= A B))
; do not do sygus inference due to uninterpreted sorts
(check-sat)
(exit)
