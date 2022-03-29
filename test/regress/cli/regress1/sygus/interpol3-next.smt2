; COMMAND-LINE: --produce-interpolants --interpolants-mode=default --check-interpolants -i
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic LIA)
(declare-fun a () Int)
(assert (> a 1))
(get-interpolant A (> a 0))
(get-interpolant-next)
