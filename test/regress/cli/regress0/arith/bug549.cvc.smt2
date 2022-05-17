; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun a () Real)
(declare-fun b () Real)
(check-sat-assuming ( (not (= (^ (* a b) 5) (* (* (* (* (* (* (* (* (* b a) a) a) a) b) b) b) b) a))) ))
