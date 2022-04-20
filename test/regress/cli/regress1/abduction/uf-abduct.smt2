; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic HO_UFLIA)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(assert (and (<= 0 a) (< a 4)))
(get-abduct ensureF (or (> (f 0) 0) (> (f 1) 0) (> (f 2) 0) (> (f 3) 0)))
