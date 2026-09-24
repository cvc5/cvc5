; DISABLE-TESTER: alethe
; COMMAND-LINE: --parse-define-fun-macros --check-proofs
; EXPECT: unsat
(set-logic UFLIA)
(define-fun f ((x Int)) Int (+ x 1))
(define-fun g () Int 3)
(declare-fun a () Int)
(assert (< (f a) a))
(assert (> (f g) 0))
(check-sat)
