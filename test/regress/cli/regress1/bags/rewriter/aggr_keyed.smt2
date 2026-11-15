; REQUIRES: unrestricted-mode
; AGGREGATE_KEYED: the columns of a bag.setof are a key of it, so each group of
; the aggregate by both columns is one row, and the aggregate is a map of its
; table
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
; column 0, column 1, COUNT(*) by columns 0 and 1
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) (+ ((_ tuple.select 2) acc) 1)))
(assert (not (= ((_ table.aggr 0 1) f (tuple 0 0 0) (bag.setof X))
                (bag.map (lambda ((t (Tuple Int Int)))
                           (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 1))
                         (bag.setof X)))))
(check-sat)
