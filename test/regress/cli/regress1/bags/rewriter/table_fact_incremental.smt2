; REQUIRES: unrestricted-mode
; The same key and query in two scopes: the lemma of the first scope is popped
; with it, and the second scope learns it again
; EXPECT: unsat
; EXPECT: unsat
(set-logic HO_ALL)
(set-option :incremental true)
(declare-const X (Bag (Tuple Int Int)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t)
         (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
         (+ ((_ tuple.select 2) acc) 1)))
(push)
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0 0) X)
                (bag.map (lambda ((t (Tuple Int Int)))
                           (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 1))
                         X))))
(check-sat)
(pop)
(push)
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0 0) X)
                (bag.map (lambda ((t (Tuple Int Int)))
                           (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 1))
                         X))))
(check-sat)
(pop)
