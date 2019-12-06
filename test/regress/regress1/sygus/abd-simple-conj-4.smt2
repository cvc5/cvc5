; COMMAND-LINE: --produce-abducts --sygus-core-connective
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic QF_LIA)
(set-option :produce-abducts true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun w () Int)
(declare-fun u () Int)
(declare-fun v () Int)
(assert (>= x 0))
(get-abduct A (>= (+ x y z w u v) 2))
