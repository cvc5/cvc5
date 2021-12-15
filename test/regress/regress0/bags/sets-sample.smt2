; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)

(define-sort SetInt () (Bag Int))

; Something simple to test parsing
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

(check-sat)

(pop 1)

; UF can tell that this is UNSAT (bag.union_disjoint)
(push 1)

(declare-fun x () (Bag Int))
(declare-fun y () (Bag Int))
(declare-fun z () (Bag Int))

(assert (= x y))
(assert (not (= (bag.union_disjoint x z) (bag.union_disjoint y z))))

(check-sat)

(pop 1)

; UF can tell that this is UNSAT (containment)
(push 1)

(declare-fun x () (Bag Int))
(declare-fun y () (Bag Int))
(declare-fun e1 () Int)
(declare-fun e2 () Int)

(assert (= x y))
(assert (= e1 e2))
(assert (>= (bag.count e1 x) 1))
(assert (not (>= (bag.count e2 y) 1)))

(check-sat)

(pop 1)

; UF can tell that this is UNSAT (merge bag.union_disjoint + containment examples)
(push 1)

(declare-fun x () (Bag Int))
(declare-fun y () (Bag Int))
(declare-fun z () (Bag Int))
(declare-fun e1 () Int)
(declare-fun e2 () Int)

(assert (= x y))
(assert (= e1 e2))
(assert (>= (bag.count e1 (bag.union_disjoint x z)) 1))
(assert (not (>= (bag.count e2 (bag.union_disjoint y z)) 1)))

(check-sat)

(pop 1)

; test all the other kinds for completeness
(push 1)

(assert
 (>=
  (bag.count 5
             (bag.union_disjoint
              (bag 1 1)
              (bag.union_disjoint
               (bag 2 1)
               (bag.union_disjoint
                (bag 3 1)
                (bag.union_disjoint (bag 4 1) (bag 5 1))))))
  1))

(assert
 (>=
  (bag.count
   5
   (bag.union_disjoint
    (bag 1 1)
    (bag.union_disjoint
     (bag 2 1)
     (bag.union_disjoint
      (bag 3 1)
      (bag.union_disjoint
       (bag 4 1)
       (as bag.empty (Bag Int)))))))
  1))

(check-sat)

(exit) 
