; REQUIRES: unrestricted-mode
; CANONICAL_VARIABLE: two filters by lambdas that differ only in the names of
; their variables are one term, and so are the aggregates over them
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0) (bag.filter (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 1) s) 3)) X))
                ((_ table.aggr 0) f (tuple 0 0) (bag.filter (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 1) t) 3)) X)))))
(check-sat)
