; COMMAND-LINE: --strings-print-ascii --strings-exp
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)
(declare-fun x () String)
(assert
(and 
(not (= 
  (str.in_re x (re.++ (str.to_re "B") (re.* (str.to_re "B")))) 
  (str.in_re x (re.++ (str.to_re "B") (str.to_re (str.++ "B" "B"))))
)) 
(not (= 
  (str.in_re x (re.++ (re.union (re.++ (str.to_re "A") re.allchar ) re.allchar ) (str.to_re "B"))) 
  (str.in_re x (re.++ (str.to_re "A") (str.to_re "B")))
))
)
)
(check-sat)
