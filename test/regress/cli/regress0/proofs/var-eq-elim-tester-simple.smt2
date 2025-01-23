; EXPECT: unsat
(set-logic ALL)
(declare-datatype List ((cons (head Int) (tail List)) (nil)))
(declare-fun P (List List) Bool)
(assert (forall ((y List) (x List)) (=> ((_ is cons) x) (P x y))))
(assert (not (P (cons 0 nil) nil)))
(check-sat)
