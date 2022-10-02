(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))

(assert (not (= x y)))

(check-sat)
