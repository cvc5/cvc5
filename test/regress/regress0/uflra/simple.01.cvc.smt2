; EXPECT: sat
(set-logic ALL)
(set-option :incremental true)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun f (Real) Real)
(push 1)

(assert (not (= (f x) (f y))))

(check-sat)

(pop 1)

