; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x () Int)
(check-sat)
(define-const t Bool (not (= x 0)))
(assert t)
(check-sat)
