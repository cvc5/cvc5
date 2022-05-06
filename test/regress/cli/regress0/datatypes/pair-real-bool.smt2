; EXPECT: sat
;(set-option :produce-models true)
(set-logic QF_ALL)
(set-info :status sat)
(declare-datatypes ((RealTree 0)) (
  (
    (Node
      (left RealTree)
      (elem Real)
      (right RealTree))
    (Leaf)
   )
))

(declare-datatypes ((Pair 2)) ((par (T1 T2) ((mk-pair (first T1) (second T2))))))

(declare-fun SumeAndPositiveTree (RealTree) (Pair Real Bool))

(declare-fun l1 () RealTree)
(declare-fun l2 () RealTree)
(declare-const result (Pair Real Bool))
(assert (= l1 (Node l2 5.0 l2)))
(assert (= result (SumeAndPositiveTree l1)))
(assert (= (first result) 5.0))
(assert (= (second result) true))
(check-sat)
