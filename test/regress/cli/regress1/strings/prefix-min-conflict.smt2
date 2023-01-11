(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)

(assert
(str.in_re w (re.++ (re.* re.allchar) (str.to_re "ABC"))))

(assert
(or
  (= w (str.++ x y z))
  (= w (str.++ z y x))
  (= w (str.++ x z y))
)
)

(assert
(or (= x "D") (= x "E") (= x "F"))
)
(assert
(or (= y "D") (= y "E") (= y "F"))
)
(assert
(or (= z "D") (= z "E") (= z "F"))
)

(check-sat)
