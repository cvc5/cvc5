; REQUIRES: unrestricted-mode
; DISABLE-TESTER: cpc
; (the cpc proof signature has no table.aggr)
; MAP_EQUAL_COLUMNS: a map over a filter that equates columns 0 and 2 reads
; the first of them, so the two maps below, and the aggregates over them,
; are one term
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int Int)))
(define-fun P ((s (Tuple Int Int Int))) Bool (= ((_ tuple.select 0) s) ((_ tuple.select 2) s)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0)
                   (bag.map (lambda ((t (Tuple Int Int Int)))
                              (tuple ((_ tuple.select 2) t) ((_ tuple.select 1) t)))
                            (bag.filter P X)))
                ((_ table.aggr 0) f (tuple 0 0)
                   (bag.map (lambda ((t (Tuple Int Int Int)))
                              (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
                            (bag.filter P X))))))
(check-sat)
