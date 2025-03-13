; EXPECT: unsat
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (distinct (str.prefixof x (str.at y z)) (str.suffixof x (str.substr y z 1))))
(check-sat)
