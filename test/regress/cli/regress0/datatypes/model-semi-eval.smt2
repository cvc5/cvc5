; COMMAND-LINE: --produce-models
; EXPECT: sat
; EXPECT: (((head (node (- x 1))) 4))
(set-logic ALL)
(declare-datatype list ((node (data Int)) (cons (head Int) (tail list))))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> y 100))
(assert (= (head (node y)) 4))
(assert (<= y x (+ y 1)))
(assert (not (= x y)))
(check-sat)
(get-value ((head (node (- x 1)))))
