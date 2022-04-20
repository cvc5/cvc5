(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)
(set-option :strings-exp true)
(declare-fun x () String)

(assert
(not (= (str.in_re x (re.++ (re.++ re.allchar  re.allchar ) (re.* re.allchar ))) (not (str.in_re x (re.* (str.to_re "A")))))
))

(check-sat)
