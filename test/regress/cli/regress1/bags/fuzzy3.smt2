(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-fun A () (Bag (Tuple Int Int)))
(declare-fun B () (Bag (Tuple Int Int)))
(declare-fun c () Int)
(declare-fun d () (Tuple Int Int))
(assert
  (not
    (=
      (= A (bag.difference_remove (bag d c) A))
      (= A (bag (tuple c c) c)))))
(check-sat)
