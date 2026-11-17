; REQUIRES: unrestricted-mode
; COMMAND-LINE: --proof-define-fun-macros --check-proofs
; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic UFLIA)
(define-fun g ((x Int)) Int (* 2 x))
(define-fun-rec sum ((x Int)) Int (ite (<= x 0) 0 (+ (g x) (sum (- x 1)))))
(assert (> (sum 0) 0))
(check-sat)
