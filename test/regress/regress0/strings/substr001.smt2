(set-logic QF_S)
(set-option :strings-exp true)
(set-info :status sat)

(declare-fun x () String)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun i4 () Int)

(assert (= "efg" (str.sub x i1 i2) ) )
(assert (= "bef" (str.sub x i3 i4) ) )
(assert (> (str.len x) 5))

(check-sat)
