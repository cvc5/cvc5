(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (= (str.len x) 1))
(assert (= (str.++ x y "b" z) "aaaba"))
(check-sat)
