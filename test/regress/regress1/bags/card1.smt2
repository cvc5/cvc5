(set-logic ALL)
(set-option :fmf-bound true)
(set-option :produce-models true)
(set-info :status sat)
(declare-fun A () (Bag String))
(assert (= (bag.card A) 10000000))
(check-sat)

