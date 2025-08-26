; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(set-option :produce-interpolants true)
(declare-fun x () Int)
(assert (= 0 x))
(get-interpolant A (= 0 x))
