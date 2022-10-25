(set-logic ALL)
(declare-fun x () Int)
(get-abduct A (> x 0) 
  ((Start Bool) (StartC Int)) (
    (Start Bool ((> x StartC))) 
    (StartC Int ((Constant Int)))))
