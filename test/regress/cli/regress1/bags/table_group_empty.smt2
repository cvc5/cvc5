; REQUIRES: unrestricted-mode
; The parts of a partition are not empty, so an empty table has no groups and
; an aggregate of it has no rows, as SQL's GROUP BY. SQL's aggregate without
; GROUP BY is a fold, one row also for an empty table.
(set-logic HO_ALL)
(set-info :status unsat)
(define-fun E () (Table Int Int) (as bag.empty (Table Int Int)))
(define-fun B () (Table Int Int) (bag (tuple 1 5) 2))
; k, SUM(v), COUNT(*) by k
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t)
         (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
         (+ ((_ tuple.select 2) acc) 1)))
; SUM(v), COUNT(*) of all rows
(define-fun g ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 1) t))
         (+ ((_ tuple.select 1) acc) 1)))
(define-fun r ((x (Tuple Int Int)) (y (Tuple Int Int))) Bool
  (= ((_ tuple.select 0) x) ((_ tuple.select 0) y)))
(assert
 (not
  (and
   ; no parts
   (= ((_ table.group 0) E) (as bag.empty (Bag (Table Int Int))))
   (= (table.group E) (as bag.empty (Bag (Table Int Int))))
   (= ((_ table.group 0) E) (bag.partition r E))
   ; no rows: SELECT k, SUM(v), COUNT(*) FROM E GROUP BY k
   (= ((_ table.aggr 0) f (tuple 0 0 0) E) (as bag.empty (Table Int Int Int)))
   (= (table.aggr g (tuple 0 0) E) (as bag.empty (Table Int Int)))
   ; one row: SELECT SUM(v), COUNT(*) FROM E
   (= (bag (bag.fold g (tuple 0 0) E) 1) (bag (tuple 0 0) 1))
   ; an aggregate of a union of tables with disjoint keys is the union of the
   ; aggregates, also when a table is empty
   (= ((_ table.aggr 0) f (tuple 0 0 0) (bag.union_disjoint E B))
      (bag.union_disjoint ((_ table.aggr 0) f (tuple 0 0 0) E)
                          ((_ table.aggr 0) f (tuple 0 0 0) B)))
   ; a nonempty table: one row per group
   (= ((_ table.aggr 0) f (tuple 0 0 0) B) (bag (tuple 1 10 2) 1))
   (= ((_ table.group 0) B) (bag B 1)))))
(check-sat)
