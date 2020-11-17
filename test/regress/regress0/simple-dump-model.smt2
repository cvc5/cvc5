; COMMAND-LINE: --dump-models
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun x () Int 1)
; EXPECT: (define-fun y () Int 1)
; EXPECT: )
(set-logic QF_LIA)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (<= x y) (> x 0)))
(assert (= y 1))
(check-sat)
