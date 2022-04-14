(set-logic ALL)
(set-option :produce-models true)
(set-info :status sat)
(declare-fun A () (Table Int Int))
(declare-fun c () Int)
(declare-fun d () (Tuple Int Int))
(assert
 (not
  (=
   (= A (bag d (+ c (bag.count d (bag.union_disjoint A A)))))
   (= A (bag.difference_remove (bag d c) A)))))
(assert (= A (bag (tuple 0 0) 5)))
(assert (= c (- 5)))
(assert (= d (tuple 0 0)))
(check-sat)
