(set-logic ALL)
(set-info :status sat)

(declare-fun x () String)
(assert (= (str.to_int x) 12345)) 
(check-sat)
