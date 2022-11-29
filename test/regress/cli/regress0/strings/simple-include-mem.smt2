; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(assert (str.in_re s (re.* (str.to_re "A"))))
(assert (not (str.in_re s (re.* (re.range "A" "Z")))))
(check-sat)
