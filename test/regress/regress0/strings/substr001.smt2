(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun i4 () Int)

(assert (= "efg" (str.substr x i1 i2) ) )
(assert (= "bef" (str.substr x i3 i4) ) )
(assert (> (str.len x) 5))

(check-sat)
