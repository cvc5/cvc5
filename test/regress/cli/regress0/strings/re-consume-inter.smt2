; EXPECT: unsat
(set-logic ALL)
(declare-fun k () String)
(assert (str.in_re 
(str.++ "a.13" k ".b") 
(re.++ (str.to_re "a.") (re.inter (re.* (re.range "0" "9")) (re.++ (re.* re.allchar) (str.to_re "3"))) (str.to_re ".b"))
))
(assert (or (= k "a") (= k "b")))
(check-sat)
