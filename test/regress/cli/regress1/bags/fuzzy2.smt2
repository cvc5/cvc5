(set-logic ALL)
(set-info :status sat)
(declare-fun a () (Table Int Int))
(declare-fun b () (Table Int Int))
(declare-fun c () Int)
(declare-fun d () (Tuple Int Int))
(assert
  (let ((D (bag d c))) ; when c = zero, then D is empty
    (and
      (= a (bag (tuple 1 1) c)) ; when c = zero, then a is empty
      (= a (bag.union_max a D))
      (= a (bag.difference_subtract a (bag d 1)))
      (= a (bag.union_disjoint a D))
      (= a (bag.inter_min a D)))))
(check-sat)
