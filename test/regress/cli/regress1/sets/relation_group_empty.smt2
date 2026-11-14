; REQUIRES: unrestricted-mode
; The parts of a partition are not empty, so an empty relation has no groups
; and an aggregate of it has no elements, as SQL's GROUP BY. SQL's aggregate
; without GROUP BY is a fold, one row also for an empty relation. The terms are
; ground: a wrong value makes the problem unsat.
(set-logic HO_ALL)
(set-info :status sat)
(define-fun E () (Relation Int Int) (as set.empty (Relation Int Int)))
; k, SUM(v) by k
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
; SUM(v) of all rows
(define-fun g ((t (Tuple Int Int)) (acc Int)) Int
  (+ acc ((_ tuple.select 1) t)))
; no parts
(assert (= ((_ rel.group 0) E) (as set.empty (Set (Relation Int Int)))))
(assert (= (rel.group E) (as set.empty (Set (Relation Int Int)))))
; no elements
(assert (= ((_ rel.aggr 0) f (tuple 0 0) E) (as set.empty (Relation Int Int))))
; one element
(assert (= (set.singleton (set.fold g 0 E)) (set.singleton 0)))
; a nonempty relation: one element per group
(assert (= ((_ rel.aggr 0) f (tuple 0 0) (set.singleton (tuple 1 5)))
           (set.singleton (tuple 1 5))))
(check-sat)
