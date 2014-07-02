(set-logic AUFLIRA)

(declare-fun f ((Array Int Bool)) Bool)
(declare-fun y () (Array Int Bool))

(assert (forall ((x (Array Int Bool))) (f y)))

(check-sat)
