; EXPECT: unsat
(set-logic ALL)
(declare-const X String)
(assert (str.in_re X (re.range "3" "3")))
(assert (str.in_re X (str.to_re "")))
(check-sat)
