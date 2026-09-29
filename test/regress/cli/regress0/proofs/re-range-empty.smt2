; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(assert (str.in_re s (re.range "Z" "A")))
(check-sat)
