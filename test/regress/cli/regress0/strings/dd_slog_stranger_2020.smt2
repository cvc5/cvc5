; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (= "" (str.++ "" x)))
(assert (str.in_re (str.++ (str.++ "f" x) "f") (re.++ (re.* re.allchar) (re.++ (str.to_re "{") (re.* re.allchar)))))
(check-sat)
