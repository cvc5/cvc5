; REQUIRES: unrestricted-mode
; A key on columns 2 0 of X: the rewriter of the theory leaves the assertion
; as a map that puts the columns of a set back in order
; (SETOF_PROJECTION_SORT), which still states the key {0, 2}
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int Int)))
(assert (= (bag.setof ((_ table.project 2 0) X)) ((_ table.project 2 0) X)))
; column 0, column 2, COUNT(*) by columns 0 and 2
(define-fun f ((t (Tuple Int Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t) (+ ((_ tuple.select 2) acc) 1)))
(assert (not (= ((_ table.aggr 0 2) f (tuple 0 0 0) X)
                (bag.map (lambda ((t (Tuple Int Int Int)))
                           (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t) 1))
                         X))))
(check-sat)
