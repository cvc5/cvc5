; EXPECT: unsat
(set-logic ALL)
(declare-fun _7 () String)
(declare-fun x () String)
(assert (= "" (str.++ _7 _7)))
(assert (= (str.++ "{" _7) (str.++ x "")))
(assert (str.in_re (str.++ x (str.++ x "")) (re.++ (re.* re.allchar) (re.++ (str.to_re "3c") (re.* re.allchar)))))
(check-sat)
