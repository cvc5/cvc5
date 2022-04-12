; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-sort A 0)
(declare-sort B 0)
(declare-fun x () A)
(declare-fun y () A)
(declare-fun f (A) B)
(check-sat-assuming ( (not (=> (= x y) (= (f x) (f y)))) ))
