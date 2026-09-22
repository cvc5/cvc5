; EXPECT: unsat
(set-logic ALL)
(declare-fun u () String)
(assert (and (not (= 0 (ite (str.contains (str.substr u 0 1) "A") 1 0))) (not (= 0 (ite (= "" (str.replace (str.substr u 0 1) "A" "a")) 1 0)))))
(check-sat)
