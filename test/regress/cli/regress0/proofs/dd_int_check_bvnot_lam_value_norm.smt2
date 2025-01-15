; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(define-fun l ((s Int) (x Int) (t Int) (x0 Int)) Bool (= x 0))
(define-fun n ((s Int) (t Int) (x0 Int)) Bool (and false (l 0 0 0 0)))
(assert (n 0 0 0))
(check-sat)
