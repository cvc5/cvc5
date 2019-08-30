; COMMAND-LINE: --strings-print-ascii --strings-exp
; EXPECT: sat
(set-info :smt-lib-version 2.5)
(set-logic ALL)
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
