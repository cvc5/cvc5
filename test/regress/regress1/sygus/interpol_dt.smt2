; COMMAND-LINE: --produce-interpols=default
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
(declare-fun x () List)
(declare-fun y () List)
(assert (= x (cons 0 nil)))
(assert (= x y))
(get-interpol A (distinct y nil))
