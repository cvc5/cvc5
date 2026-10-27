; EXPECT: sat
(set-logic ALL)
(declare-fun a () String)
(assert (str.in_re a (re.range "A" "Z")))
(assert (str.in_re a (re.inter (re.comp (re.range "A" "J")) (re.range "A" "Z"))))
(check-sat)
