(set-info :smt-lib-version 2.5)
(set-logic ALL)
(set-info :status sat)
(set-option :strings-exp true)
(declare-fun x () String)

(assert
(not (= (str.in.re x (re.++ (re.++ re.allchar  re.allchar ) (re.* re.allchar ))) (not (str.in.re x (re.* (str.to.re "A")))))
))

(check-sat)
