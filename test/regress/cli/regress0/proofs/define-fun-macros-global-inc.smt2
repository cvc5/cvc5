; DISABLE-TESTER: alethe
; COMMAND-LINE: --parse-define-fun-macros -i --global-declarations
; EXPECT: unsat
; EXPECT: unsat
(set-logic UFLIA)
(declare-fun a () Int)
(push)
(define-fun f ((x Int)) Int (+ x 1))
(assert (< (f a) a))
(check-sat)
(pop)
(assert (< (f a) a))
(check-sat)
