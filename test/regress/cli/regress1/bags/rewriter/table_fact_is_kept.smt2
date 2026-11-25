; REQUIRES: unrestricted-mode
; CPC checking fails because the signature does not define table.project.
; DISABLE-TESTER: cpc
; The lemma of the key of X rewrites the aggregate by it to a map of X, and
; the assertion of the key stays: two rows of X with column 0 equal to 1
; contradict it, and without it the problem is sat
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
(declare-const Z (Bag (Tuple Int Int Int)))
(declare-const W (Bag (Tuple Int Int Int)))
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t)
         (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
         (+ ((_ tuple.select 2) acc) 1)))
; not a substitution, so the aggregate stays in the input
(assert (or (= Z ((_ table.aggr 0) f (tuple 0 0 0) X)) (= Z W)))
(assert (= (bag.count (tuple 1) ((_ table.project 0) X)) 2))
(check-sat)
