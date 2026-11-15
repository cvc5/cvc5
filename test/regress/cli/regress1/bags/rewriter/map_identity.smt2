; REQUIRES: unrestricted-mode
; MAP_IDENTITY: the map that copies every column in order is its argument, so
; the aggregates over the two are one term
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0)
                   (bag.map (lambda ((t (Tuple Int Int)))
                              (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
                            X))
                ((_ table.aggr 0) f (tuple 0 0) X))))
(check-sat)
