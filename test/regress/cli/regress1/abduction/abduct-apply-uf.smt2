; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(set-option :produce-abducts true)
(declare-fun x (Int) Bool)
(assert (x 0))
(get-abduct A (x 0))
