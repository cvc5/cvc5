; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-fun x () List)
(assert (distinct x nil))
(get-abduct A (= x (cons (head x) (tail x))))
