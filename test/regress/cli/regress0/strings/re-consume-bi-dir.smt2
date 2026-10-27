; EXPECT: unsat
(set-logic ALL)
(declare-fun k () String)
(assert (not (str.in_re 
(str.++ "d.1.a" k "3") 
(re.++ (str.to_re "d.") (re.* (re.range "0" "9")) (str.to_re ".") (re.* re.allchar))
)))
(check-sat)
