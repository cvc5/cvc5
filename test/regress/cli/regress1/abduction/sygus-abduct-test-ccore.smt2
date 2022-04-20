; COMMAND-LINE: --produce-abducts --sygus-core-connective
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0

(set-logic QF_UFLIRA)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (>= n 1))
(assert (and (<= n x)(<= x (+ n 5))))
(assert (and (<= 1 y)(<= y m)))

(get-abduct A (not (< x y)))
