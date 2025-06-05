; EXPECT: unsat
(set-logic ALL)
(declare-fun v () String)
(assert (str.in_re (str.++ v v) (re.++ (str.to_re "a") (re.union (str.to_re "") (re.++ (str.to_re "z") (re.union (str.to_re "") (str.to_re "a")))))))
(check-sat)
