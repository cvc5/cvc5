; REQUIRES: unrestricted-mode
; A lambda that ignores its arguments is a function constant, so each term
; below has constant children and is evaluated by BagsUtils::evaluate. The
; terms are ground: a wrong value makes the problem unsat.
(set-logic HO_ALL)
(set-info :status sat)
(define-fun A () (Bag Int) (bag.union_disjoint (bag 1 2) (bag 3 1)))
(define-fun X () (Bag (Tuple Int Int))
  (bag.union_disjoint (bag (tuple 1 2) 1) (bag (tuple 1 3) 1) (bag (tuple 4 5) 1)))
(assert (bag.all (lambda ((x Int)) true) A))
(assert (not (bag.all (lambda ((x Int)) false) A)))
(assert (bag.some (lambda ((x Int)) true) A))
(assert (not (bag.some (lambda ((x Int)) false) A)))
(assert (= (bag.partition (lambda ((a Int) (b Int)) true) A) (bag A 1)))
; one row (tuple 7) for each of the groups 1 and 4 of column 0
(assert (= ((_ table.aggr 0) (lambda ((t (Tuple Int Int)) (acc (Tuple Int))) (tuple 7))
                             (tuple 0)
                             X)
           (bag (tuple 7) 2)))
(check-sat)
