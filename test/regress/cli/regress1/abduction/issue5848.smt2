; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-fun a () Int)
(assert (= (mod 0 a) 0))
(get-abduct A (= a 1))
