; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(set-option :produce-abducts true)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (= (>= b c) (>= 0 a)))
(assert (= c a))
(get-abduct d (<= a b))
