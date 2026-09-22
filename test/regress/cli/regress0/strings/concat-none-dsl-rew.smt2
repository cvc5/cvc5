; EXPECT: unsat
(set-logic ALL)
(declare-const s String)
(assert (> (str.len s) 0))
(assert (str.in_re s (re.* (re.++ (str.to_re "A") (re.++ re.none (str.to_re "A")) (str.to_re "B")))))
(check-sat)
