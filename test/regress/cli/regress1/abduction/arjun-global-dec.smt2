; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0

(set-option :produce-models true)
(set-option :global-declarations true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-logic QF_LIA)
(declare-fun y () Int)
(define-fun x!0 () Bool (<= 0 y))
(declare-fun x () Int)
(declare-fun z () Int)
(define-fun x!1 () Int (+ z y x))
(define-fun x!2 () Bool (<= 0 x!1))
(assert x!0)
(get-abduct abd x!2)
(get-abduct-next)
