; COMMAND-LINE: --sygus-inference
; EXPECT: sat
(set-logic ALL)
(define-sort SB () (S Bool))
(declare-fun A () (S Bool))
(declare-fun B () SB)
(assert (= A B))
; reject due to uninterpreted sorts
(check-sat)
(exit)
