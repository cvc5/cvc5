; EXPECT: unsat
(set-logic ALL)
(declare-const s String)
(assert (str.in_re s (re.* (re.++ re.allchar re.allchar re.allchar))))
(assert (= (str.len s) 10))
(check-sat)
