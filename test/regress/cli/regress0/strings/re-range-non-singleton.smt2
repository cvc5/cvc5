; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(assert (or (str.in_re s (re.range "ABC" "D")) (str.in_re s (re.range "A" "BCD"))))
(check-sat)
