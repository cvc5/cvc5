; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(assert (= (str.++ "0" (str.from_code 0) "AA") (str.++ a "0" (str.at (str.++ a a) 1) "A")))
(check-sat)
