; COMMAND-LINE: --produce-interpols=default
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0

(set-logic ALL)
;(declare-fun n () Int) ; n = A[0]
;(declare-fun m () Int) ; m = A[1]
;(declare-fun x () Int) ; x = A[2]
;(declare-fun y () Int) ; y = A[3]

(declare-fun arr () (Array Int Int))

(assert (>= (select arr 0) 1))
(assert (and (<= (select arr 0) (select arr 2))(<= (select arr 2) (+ (select arr 0) 5))))
(assert (and (<= 1 (select arr 3))(<= (select arr 3) (select arr 1))))

(get-abduct A (not (< (select arr 2) (select arr 3))))

