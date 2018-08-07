(set-info :smt-lib-version 2.5)
(set-logic ALL)
(set-option :strings-exp true)
(set-info :status sat)
(declare-fun x () String)
(assert
(and 
(not (= 
  (str.in.re x (re.++ (str.to.re "B") (re.* (str.to.re "B")))) 
  (str.in.re x (re.++ (str.to.re "B") (str.to.re (str.++ "B" "B"))))
)) 
(not (= 
  (str.in.re x (re.++ (re.union (re.++ (str.to.re "A") re.allchar ) re.allchar ) (str.to.re "B"))) 
  (str.in.re x (re.++ (str.to.re "A") (str.to.re "B")))
))
)
)
(check-sat)
(get-model)
