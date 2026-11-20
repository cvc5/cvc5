; REQUIRES: unrestricted-mode
; AGGREGATE_CONSTANT_COLUMNS: a column that the step sets to a constant has
; that constant in the row of every group, so a map above the aggregate of the
; other columns writes it.
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
; column 0 of X, the constant 7, and the sum of column 1
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t)
         7
         (+ ((_ tuple.select 2) acc) ((_ tuple.select 1) t))))
; column 0 of X and the sum of column 1
(define-fun g ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t)
         (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0 0) X)
                (bag.map
                  (lambda ((r (Tuple Int Int)))
                    (tuple ((_ tuple.select 0) r) 7 ((_ tuple.select 1) r)))
                  ((_ table.aggr 0) g (tuple 0 0) X)))))
(check-sat)
