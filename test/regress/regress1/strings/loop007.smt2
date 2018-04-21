(set-logic QF_S)
(set-option :strings-exp true)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)

(assert (= (str.++ x y "aa") (str.++ "aa" y x)))
(assert (= (str.len x) (* 2 (str.len y))))
(assert (> (str.len x) 0))

(check-sat)
