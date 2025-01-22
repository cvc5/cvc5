; EXPECT: unsat
(set-logic ALL)
(declare-fun u () String)
(assert (not (= 0 (ite (= "pr" (str.replace (str.substr u 0 1) "A" "")) 1 0))))
(check-sat)
