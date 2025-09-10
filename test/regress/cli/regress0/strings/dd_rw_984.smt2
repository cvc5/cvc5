; EXPECT: unsat
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (distinct (str.replace (str.replace "A" x y) "B" y) (str.replace "A" x (str.replace y "B" y))))
(check-sat)
