; COMMAND-LINE: --produce-interpols=default --sygus-active-gen=enum --check-interpols
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0

(set-logic QF_UFLIA)

; Let A1,...,An be formulas (called assumptions)
; Let C be a formula (called a conjecture)
; An interpolant of {A1,...,An} and G is any formula B such that:
; - A1,...,An |- B
; - B |- C
; - B has only variables that occur both in {A_1,...,A_n} and B.

;The variables used are n,m,x,y, all integers.
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun x () Int)
(declare-fun y () Int)

;The assumptions are:
; (*) 1 <= n <= x <= n+5
; (*) 1 <= y <= m
(define-fun A1 () Bool (<= 1 n))
(define-fun A2 () Bool (<= n x))
(define-fun A3 () Bool (<= x (+ n 5)))
(define-fun A4 () Bool (<= 1 y))
(define-fun A5 () Bool (<= y m))
(assert (and A1 A2 A3 A4 A5))

;The conjuecture is: 2 <= x+y
(get-interpol A (<= 2 (+ x y)))
