; COMMAND-LINE: --fmf-fun
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)

(define-fun-rec p2 ((n Int) (p Int)) Bool (
	or
	(and (= n 0) (= p 1))
	(and (> n 0) (> p 1) (= 0 (mod p 2)) (p2 (- n 1) (div p 2)))
))

(declare-const n Int)
(declare-const p Int)

(assert (= n 10))
(assert (p2 n p))

(check-sat)
