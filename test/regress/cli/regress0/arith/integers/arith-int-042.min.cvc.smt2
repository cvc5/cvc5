; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x1 () Int)
(declare-fun x0 () Int)
(check-sat-assuming ( (= (+ (* x0 6) (* x1 32)) 1) ))
