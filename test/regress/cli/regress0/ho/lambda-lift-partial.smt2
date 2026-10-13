; REQUIRES: unrestricted-mode
; COMMAND-LINE: --check-proofs --proof-check=eager
; EXPECT: unsat
(set-logic HO_ALL)
(declare-fun g (Int Int) Int)
(assert (= (@ g 0) (lambda ((x Int)) (+ 1 (g 0 x)))))
(check-sat)
