(set-logic QF_UFSLIA)
(set-info :status sat)
(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))
(declare-fun f ((Seq Int)) (Seq Bool))

(assert (not (= x y)))
(assert (not (= (f x) (f y))))

(check-sat)
