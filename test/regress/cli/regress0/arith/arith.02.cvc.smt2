; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(check-sat-assuming ( (not (= (* x (* y z)) (* (* x y) z))) ))
