; EXPECT: unsat
(set-logic QF_S)
(declare-fun v () String)
(declare-fun a () String)
(assert (str.in_re (str.++ v a) (re.* (re.++ (str.to_re "b") (str.to_re "z")))))
(assert (str.in_re v (str.to_re "a")))
(check-sat)
