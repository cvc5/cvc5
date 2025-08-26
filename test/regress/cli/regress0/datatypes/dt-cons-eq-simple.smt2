; EXPECT: unsat
(set-logic ALL)

(declare-datatype List ((cons (head Int) (tail List)) (nil)))

(declare-fun x () Int)
(declare-fun y () Int)

(assert (not (= x y)))
(assert (= (cons x nil) (cons y nil)))
(check-sat)
