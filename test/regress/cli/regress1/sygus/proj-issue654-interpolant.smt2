; COMMAND-LINE: --produce-interpolants
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(set-option :produce-interpolants true)
(set-option :incremental true)
(declare-fun x () Real)
(assert (< 7972974285720917.0 x))
(get-interpolant A (< 7972974285720917.0 x))
