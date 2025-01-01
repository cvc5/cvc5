; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(define-fun P ((x Int) (x Int)) Bool (= x 0))
(assert (P 0 1))
(check-sat)
