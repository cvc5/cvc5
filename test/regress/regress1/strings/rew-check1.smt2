(set-info :smt-lib-version 2.5)
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(assert (not (=
(str.in.re x (re.++ (re.* re.allchar ) (str.to.re "A")  (re.* re.allchar ) re.allchar  (re.* re.allchar ) (re.* (str.to.re "A")) (re.* re.allchar ))) 
(str.in.re x (re.++ (re.* (str.to.re "A")) (re.* (str.to.re "B")) (re.* re.allchar ) (str.to.re "A")  (re.* re.allchar ) re.allchar  (re.* re.allchar )))
)))

(check-sat)
