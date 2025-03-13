; EXPECT: unsat
(set-logic ALL)
(declare-fun p (Int) Int)
(define-fun i ((k Int) (a Int)) Int (p 0))
(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool (= 0 (i k x)))
(define-fun n ((k Int) (t Int) (x Int)) Bool (and false (l 0 0 0 0)))
(assert (n 0 0 0))
(check-sat)
