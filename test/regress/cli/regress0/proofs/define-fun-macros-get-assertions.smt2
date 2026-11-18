; COMMAND-LINE: --proof-define-fun-macros
; EXPECT: (
; EXPECT: (= f (lambda ((x Int)) (+ x 1)))
; EXPECT: (P (+ a 1))
; EXPECT: (P (f a))
; EXPECT: )
(set-option :produce-assertions true)
(set-logic ALL)
(declare-fun P (Int) Bool)
(declare-fun a () Int)
(define-fun f ((x Int)) Int (+ x 1))
(assert (P (+ a 1)))
(assert (P (f a)))
(get-assertions)
