; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((List 2)) ((par (X Y)((nil) (cons (head X) (tail (List Y X)))))))
(declare-fun x () (List Int String))
(declare-fun y () (List Int String))
(assert (not (= x y)))
(assert (not (= x (tail (tail x)))))
(check-sat)
