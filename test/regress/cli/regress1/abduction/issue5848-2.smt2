; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-fun v9 () Bool)
(get-abduct A (or true v9))
