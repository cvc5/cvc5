; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun var_4 () String)
(declare-fun var_5 () String)
(assert (str.in_re (str.++ var_4 "z" var_5 ) (re.++ (re.* (re.++ (str.to_re "a") (re.++ (re.* (re.union (str.to_re "b") (str.to_re "a"))) (str.to_re "z")))) (re.++ (str.to_re "a") (re.* (re.union (str.to_re "b") (str.to_re "a")))))))
(assert (str.in_re var_5 (re.* (str.to_re "b"))))
(assert (str.in_re var_4 (re.* (str.to_re "a"))))
(check-sat)
