(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun i () Int)

(assert (= (str.at x i) "b"))
(assert (> i 5))
(assert (< (str.len x) 4))
(assert (> (str.len x) 2))

(check-sat)
