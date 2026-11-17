; COMMAND-LINE: --learned-rewrite
; REQUIRES: unrestricted-mode
; --learned-rewrite is not supported with proofs or unsat cores because
; the preprocessing pass does not track its non-local reasoning.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; AGGREGATE_KEYED by a learned fact: the assertion that column 0 is a key of X
; is a learned literal, so the learned-rewrite pass rewrites the aggregate by
; column 0 to a map of X, which the rewriter of the theory cannot do
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int Int)))
(assert (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X)))
; column 0, SUM(column 1), COUNT(*) by column 0
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int Int))) (Tuple Int Int Int)
  (tuple ((_ tuple.select 0) t)
         (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
         (+ ((_ tuple.select 2) acc) 1)))
(assert (not (= ((_ table.aggr 0) f (tuple 0 0 0) X)
                (bag.map (lambda ((t (Tuple Int Int)))
                           (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 1))
                         X))))
(check-sat)
