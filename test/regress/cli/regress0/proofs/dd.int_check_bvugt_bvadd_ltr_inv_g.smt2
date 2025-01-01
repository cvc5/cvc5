; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic QF_UFLIA)
(declare-fun p (Int) Int)
(define-fun l ((t Int) (t Int) (t Int) (t Int)) Bool (= t t))
(assert (not (l 0 0 0 (p 0))))
(check-sat)
