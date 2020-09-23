(set-logic ALL_SUPPORTED)
(set-info :status sat)
(set-option :produce-models true)

(declare-fun S () (Set Int))
(declare-fun B () (Bag Int))
(assert (not (= S   (as emptyset (Set Int)))))
(assert (not (= B   (as emptybag (Bag Int)))))
(check-sat)
