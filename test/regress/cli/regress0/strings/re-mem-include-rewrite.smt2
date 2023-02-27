; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)

(assert (not (str.in_re (str.++ x "abc" y) (re.++ (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "c")  (re.* re.allchar)))))

(check-sat)
