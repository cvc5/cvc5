; DISABLE-TESTER: alethe
; COMMAND-LINE: --parse-define-fun-macros --produce-unsat-cores
; EXPECT: unsat
; EXPECT: (
; EXPECT: A1
; EXPECT: A2
; EXPECT: )
(set-logic UFLIA)
(define-fun f ((x Int)) Int (+ x 1))
(declare-fun a () Int)
(declare-fun b () Int)
(assert (! (< (f a) b) :named A1))
(assert (! (> a b) :named A2))
(assert (! (> a 5) :named A3))
(check-sat)
(get-unsat-core)
