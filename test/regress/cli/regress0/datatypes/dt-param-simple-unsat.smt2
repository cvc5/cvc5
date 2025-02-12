; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ( (List 1) ) (
(par ( X ) ( (nil) (cons (head X) (tail (List X)))))
))
(declare-fun x () (List Int))
(assert (= (cons 0 x) (as nil (List Int))))
(check-sat)
