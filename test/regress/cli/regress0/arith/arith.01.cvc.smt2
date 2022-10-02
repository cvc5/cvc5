; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Real)
(declare-fun y () Real)
(check-sat-assuming ( (not (= (* x y) (* y x))) ))
