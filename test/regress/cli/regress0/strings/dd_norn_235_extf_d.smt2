; EXPECT: unsat
(set-logic ALL)
(declare-fun v () String)
(declare-fun a () String)
(assert (str.in_re (str.++ v "z" a) (re.++ (re.union (str.to_re "") (re.++ (str.to_re "a") (re.++ (str.to_re "z") (re.* (str.to_re "a"))))) (str.to_re "a"))))
(assert (str.in_re (str.++ v v) (re.++ (str.to_re "a") (re.union (str.to_re "") (re.++ (str.to_re "z") (re.union (str.to_re "") (str.to_re "a")))))))
(assert (str.in_re a (re.range "a" "u")))
(assert (str.in_re v (re.* (re.range "a" "u"))))
(check-sat)
