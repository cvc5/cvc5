(set-logic ALL)
(set-option :produce-models true)
(set-info :status sat)
(declare-fun A () (Bag (Tuple Int Int)))
(declare-fun B () (Bag (Tuple Int Int)))
(declare-fun c () Int)
(declare-fun d () (Tuple Int Int))
(assert
  (not
     (=
        (= A (bag d (+ c (bag.count d (union_disjoint A A)))))
        (= A (difference_remove (bag d c) A)))))
(check-sat)
; A -> (bag (tuple 0 0) 5)
; B -> (bag (tuple 0 0) 1)
; c -> (- 5)
; d -> (tuple 0 0)