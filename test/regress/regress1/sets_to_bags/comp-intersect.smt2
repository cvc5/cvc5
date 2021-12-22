; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic HO_ALL)

(set-info :status unsat)

(declare-fun x () (Bag Int))
(declare-fun y () (Bag Int))
(declare-fun bag.universe () (Bag Int))
(assert (bag.subbag x bag.universe))
(assert (bag.subbag y bag.universe))


(define-fun f1 ((z Int) (A (Bag Int))) (Bag Int)
  (ite (> z 4)
       (bag.union_disjoint (bag (* 5 z) 1) A)
       A))

(define-fun f2 ((z Int) (A (Bag Int))) (Bag Int)
  (ite (< z 10)
       (bag.union_disjoint (bag (+ (* 5 z) 1) 1) A)
       A))

;(assert (= x (bag.comprehension ((z Int)) (> z 4) (* 5 z))))
(assert (= x (bag.fold f1 (as bag.empty (Bag Int)) bag.universe)))

;(assert (= y (bag.comprehension ((z Int)) (< z 10) (+ (* 5 z) 1))))
(assert (= x (bag.fold f1 (as bag.empty (Bag Int)) bag.universe)))

(assert (not (= (bag.inter_min x y) (as bag.empty (Bag Int)))))

(check-sat)
