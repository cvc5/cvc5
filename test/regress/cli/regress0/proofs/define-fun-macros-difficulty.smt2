; COMMAND-LINE: --proof-define-fun-macros --produce-difficulty
; The difficulty map is empty when unsat cores are checked, independently of
; whether definitions are treated as macros.
; DISABLE-TESTER: unsat-core
; EXPECT: unsat
; EXPECT: (
; EXPECT: (A1 1)
; EXPECT: (A2 1)
; EXPECT: )
(set-logic ALL)
(define-fun f ((x Int)) Int (+ x 1))
(declare-fun a () Int)
(declare-fun b () Int)
(assert (! (< (f a) b) :named A1))
(assert (! (> a b) :named A2))
(check-sat)
(get-difficulty)
