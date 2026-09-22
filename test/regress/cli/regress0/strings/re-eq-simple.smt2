; EXPECT: unsat
(set-logic ALL)
(assert (= (re.union (str.to_re "A") (str.to_re "B")) (str.to_re "C")))
(check-sat)
