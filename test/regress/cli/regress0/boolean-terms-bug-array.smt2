(set-logic AUFLIRA)
(set-info :status sat)

(declare-fun f ((Array Int Bool)) Bool)
(declare-fun y () (Array Int Bool))

(assert (forall ((x (Array Int Bool))) (f y)))

(check-sat)
