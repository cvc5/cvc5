; COMMAND-LINE: --produce-interpolants --interpolants-mode=default --sygus-enum=fast --check-interpolants
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-fun arr () (Array Int Int))

(define-fun A1 () Bool (<= 1 (select arr 0)))
(define-fun A2 () Bool (<= (select arr 0) (select arr 2)))
(define-fun A3 () Bool (<= (select arr 2) (+ (select arr 0) 5)))
(define-fun A4 () Bool (<= 1 (select arr 3)))
(define-fun A5 () Bool (<= (select arr 3) (select arr 1)))
(assert (and A1 A2 A3 A4 A5))

;The conjuecture is: 2 <= x+y
(get-interpolant A (<= 2 (+ (select arr 2) (select arr 3))))
