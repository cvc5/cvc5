(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(assert (not (=
(str.in_re x (re.++ (re.* re.allchar ) (str.to_re "A")  (re.* re.allchar ) re.allchar  (re.* re.allchar ) (re.* (str.to_re "A")) (re.* re.allchar ))) 
(str.in_re x (re.++ (re.* (str.to_re "A")) (re.* (str.to_re "B")) (re.* re.allchar ) (str.to_re "A")  (re.* re.allchar ) re.allchar  (re.* re.allchar )))
)))

(check-sat)
