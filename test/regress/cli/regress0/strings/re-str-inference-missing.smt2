; EXPECT: unsat
(set-logic ALL)
(declare-fun r () String)
(assert (not (str.in_re r (re.++ (str.to_re "aa$b$c$$") (re.union (str.to_re "") ((_ re.loop 3 3) (re.range "0" "9")))))))
(assert (str.in_re r (re.++ (str.to_re "aa$b$") (re.* (re.union (re.range "a" "z") (re.range "0" "9"))) (str.to_re "$$") (re.union (str.to_re "") ((_ re.loop 3 3) (re.range "0" "9"))))))
(assert (str.in_re r (re.++ (str.to_re "aa$b$c$") (re.* re.allchar))))
(check-sat)
