; COMMAND-LINE: --produce-interpols=default
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic LIA)
(declare-fun a () Int)
(assert (> a 1))
(get-interpol A (> a 0))
