; EXPECT: sat
(set-logic QF_S)
(declare-fun v () String)
(declare-fun a () String)
(assert (str.in_re (str.++ v "z" "b" a) (re.++ (re.* (re.union (str.to_re "z") (str.to_re "a"))) (re.union (str.to_re "") (re.++ (re.union (str.to_re "b") (str.to_re "a")) (re.* (str.to_re "z")))))))
(assert (str.in_re v (re.* (re.range "a" "u"))))
(assert (not (str.contains "a" v)))
(assert (str.in_re (str.++ v "a" "z" a) (re.* (re.++ (re.* (str.to_re "a")) (str.to_re "z")))))
(check-sat)
