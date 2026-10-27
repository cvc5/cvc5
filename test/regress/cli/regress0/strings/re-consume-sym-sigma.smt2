; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (str.in_re (str.++ "abc" x "." y) (re.++ (str.to_re (str.++ "abc" x)) (re.* re.allchar) (str.to_re ".") (str.to_re y)))))
(check-sat)
