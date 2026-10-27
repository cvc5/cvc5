; EXPECT: unsat
(set-logic ALL)
(declare-const s String)
(assert (str.in_re s (re.inter 
(re.* (re.++ (re.* (str.to_re "z")) (str.to_re "b")))
(re.comp
(re.* (re.++ (re.* (re.union (str.to_re "z") (str.to_re "a"))) (str.to_re "b")))
))))
(check-sat)
