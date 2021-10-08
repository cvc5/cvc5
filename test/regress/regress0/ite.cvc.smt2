; EXPECT: unsat
(set-logic ALL)
(set-option :incremental true)
(declare-fun x () Real)
(declare-fun y () Real)
(push 1)

(assert (not (= x (ite true x y))))

(check-sat)

(pop 1)

