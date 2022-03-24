; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-sort T 0)
(declare-fun x () T)
(declare-fun y () T)
(declare-fun f (T) T)
(check-sat-assuming ( (not (let ((_let_1 (= (f x) (f y)))) (= _let_1 _let_1))) ))
