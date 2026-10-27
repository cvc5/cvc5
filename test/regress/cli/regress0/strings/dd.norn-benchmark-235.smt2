; EXPECT: unsat
(set-logic ALL)
(declare-fun v () String)
(assert (str.in_re (str.++ v v) (re.++ (str.to_re "z") (re.* (str.to_re "z")))))
(assert (str.in_re (str.++ "" v) (re.++ (re.* (str.to_re "z")) (str.to_re "a"))))
(check-sat)
