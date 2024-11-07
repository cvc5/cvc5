(set-logic QF_S)

(set-info :status sat)

(declare-fun x () String)

(assert (= (str.++ x "aa") (str.++ "aa" x)))
(assert (= (str.len x) 7))

(check-sat)
