; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic QF_LIA)
(set-option :produce-abducts true)
(set-option :incremental true)
(declare-fun x () Int)
(declare-fun y () Int)
(push)
(assert (>= x 0))
(get-abduct A (>= (+ x y) 2))
(pop)

(assert (<= x 0))
(get-abduct A (<= (+ x y) 2))
