; DISABLE-TESTER: alethe
; COMMAND-LINE: --parse-define-fun-macros --check-proofs
; EXPECT: unsat
(set-logic UFLIA)
(define-fun g ((x Int)) Int (* 2 x))
(define-fun-rec sum ((x Int)) Int (ite (<= x 0) 0 (+ (g x) (sum (- x 1)))))
(assert (> (sum 0) 0))
(check-sat)
