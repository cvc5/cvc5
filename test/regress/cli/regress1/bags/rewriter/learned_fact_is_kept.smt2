; COMMAND-LINE: --learned-rewrite
; REQUIRES: unrestricted-mode
; --learned-rewrite is not supported with proofs or unsat cores because
; the preprocessing pass does not track its non-local reasoning.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; The learned-rewrite pass rewrites the aggregate by the key of X to a map of
; X, and keeps the assertion of the key: two rows of X with column 0 equal to 1
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
; not a substitution, so the aggregate reaches the learned-rewrite pass
(assert (or (= Z ((_ table.aggr 0) f (tuple 0 0 0) X)) (= Z W)))
(assert (= (bag.count (tuple 1) ((_ table.project 0) X)) 2))
(check-sat)
