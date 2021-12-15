; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: sat
(set-option :incremental true)

(set-logic ALL)

(declare-fun x () (Bag Int))
(declare-fun y () (Bag Int))
(declare-fun z () (Bag Int))
(declare-fun e1 () Int)
(declare-fun e2 () Int)

(push 1)

(declare-fun a () (Bag Int))
(declare-fun b () (Bag Int))
(declare-fun c () (Bag Int))
(declare-fun e () Int)

(assert (= a (bag 5 1)))
(assert (= c (bag.union_disjoint a b)))
(assert (not (= c (bag.inter_min a b))))
(assert (= c (bag.difference_remove a b)))
(assert (bag.subbag a b))
(assert (>= (bag.count e c) 1))
(assert (>= (bag.count e a) 1))
(assert (>= (bag.count e (bag.inter_min a b)) 1))

(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)

(push 1)

(assert (= x y))
(assert (not (= (bag.union_disjoint x z) (bag.union_disjoint y z))))

(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)

(push 1)

(assert (= x y))
(assert (= e1 e2))
(assert (>= (bag.count e1 x) 1))
(assert (not (>= (bag.count e2 y) 1)))

(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)

(push 1)

(assert (= x y))
(assert (= e1 e2))
(assert (>= (bag.count e1 (bag.union_disjoint x z)) 1))
(assert (not (>= (bag.count e2 (bag.union_disjoint y z)) 1)))

(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)

(push 1)

(assert
  (>=
   (bag.count 5
              (bag.union_disjoint
               (bag.union_disjoint
                (bag.union_disjoint
                 (bag.union_disjoint (bag 1 1) (bag 2 1)) (bag 3 1))
                (bag 4 1))
               (bag 5 1)))
   1))

(assert
  (>=
    (bag.count 5
               (bag.union_disjoint
                (bag.union_disjoint
                 (bag.union_disjoint
                   (bag.union_disjoint
                    (bag 1 1) (bag 2 1))
                   (bag 3 1))
                 (bag 4 1))
                (as bag.empty (Bag Int))))
    1))

(push 1)

(assert true)

(check-sat)

(pop 1)

(pop 1)

(check-sat-assuming
  ((not (let ((_let_1 (>= (bag.count e1 z) 1))) (and _let_1 (not _let_1))))))
