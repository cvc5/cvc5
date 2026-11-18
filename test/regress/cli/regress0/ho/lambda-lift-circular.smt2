; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic HO_ALL)
(declare-fun f (Int) Int)
(assert (= f (lambda ((x Int)) (+ 1 (f x)))))
(check-sat)
