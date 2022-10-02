

(set-logic ALL)
(set-option :produce-models true)
(set-info :status sat)
(declare-datatypes ( (List 1) (List2 1) ) (
(par ( X ) 
( (cons (head X) (tail (List2 X))) (nil))
)
(par ( Y ) 
( (cons2 (head2 Y) (tail2 (List Y))) (nil))
)
))
(declare-fun a () (List Int))
(declare-fun b () (List Int))
(assert (= (head a) 5))
(check-sat)
