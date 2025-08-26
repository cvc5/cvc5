; EXPECT: unsat
(set-logic ALL)
(declare-fun b () String)
(assert (>= (str.to_int (str.at b 0)) 2))
(assert (str.in_re b (re.range "0" "1")))
(check-sat)
