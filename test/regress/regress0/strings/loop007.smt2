(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)

(assert (= (str.++ x y "aa") (str.++ "aa" y x)))
(assert (= (str.len x) 1))

(check-sat)