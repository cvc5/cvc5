; COMMAND-LINE: -q
; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun f ((x Int)) Bool (>= x 1))
; EXPECT: (define-fun a () Int 0)
; EXPECT: )
(set-logic HO_ALL)
(set-option :produce-models true)
(declare-fun f (Int) Bool)
(declare-fun a () Int)
(assert (and (>= a 0) (< a 2) (not (= a 1))))
(assert (or (= f (lambda ((x Int)) (> x a))) (= f (lambda ((x Int)) (< x a)))))
(assert (f 3))
(check-sat)
(get-model)
