; COMMAND-LINE: --proof-define-fun-macros --produce-difficulty
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
