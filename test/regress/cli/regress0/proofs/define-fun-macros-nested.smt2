; DISABLE-TESTER: alethe
; COMMAND-LINE: --parse-define-fun-macros
; EXPECT: unsat
(set-logic UFNIA)
(define-fun f ((x Int)) Int (+ x 1))
(define-fun h ((y Int) (z Int)) Int (* (f y) (f z)))
(define-fun c () Int (f 0))
(declare-fun a () Int)
(assert (> (h a c) (* (+ a 1) 2)))
(assert (< a 1))
(assert (> a 0))
(check-sat)
