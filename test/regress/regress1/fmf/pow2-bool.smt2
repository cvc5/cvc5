; COMMAND-LINE: --fmf-fun --no-check-models
; EXPECT: sat
(set-logic ALL)

(define-fun-rec pow2 ((n Int) (p Int)) Bool (
	or
	(and (= n 0) (= p 1))
	(and (> n 0) (> p 1) (= 0 (mod p 2)) (pow2 (- n 1) (div p 2)))
))

(declare-const n Int)
(declare-const p Int)

(assert (= n 10))
(assert (pow2 n p))

(check-sat)
