; COMMAND-LINE: --produce-abducts
; SCRUBBER: grep -v -E '(\(define-fun)'
; EXIT: 0
(set-logic ALL)
(declare-fun x () Int)
(get-abduct A (> x 0) 
  ((Start Bool) (StartC Int)) (
    (Start Bool ((> x StartC))) 
    (StartC Int ((Constant Int)))))
