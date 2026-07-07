; COMMAND-LINE: --produce-interpolants
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-fun v0 () Bool)
(assert v0)
(get-interpolant I (or v0 true))
