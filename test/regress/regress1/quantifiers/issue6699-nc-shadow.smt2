; COMMAND-LINE: -i
; EXPECT: unsat
(set-logic ALL)
(declare-fun v1 () Bool)
(declare-fun v4 () Bool)
(declare-fun v7 () Bool)
(assert (distinct v7 v1 (and v4 (exists ((q1 Int)) (= (= 0 q1) (and v7 v1))))))
(push)
(check-sat)
