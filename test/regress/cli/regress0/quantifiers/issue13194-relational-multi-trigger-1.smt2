; REQUIRES: unrestricted-mode
; COMMAND-LINE: --relational-triggers
; EXPECT: unsat
(set-logic UFLIA)
(declare-fun P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (! (P x y) :pattern ((>= x 5) (>= y 7)))))
(declare-const a Int)
(assert (>= a 5))
(assert (not (P a a)))
(check-sat)
