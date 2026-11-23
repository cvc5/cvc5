; REQUIRES: unrestricted-mode
; CPC checking fails because the signature does not define table.project.
; DISABLE-TESTER: cpc
; AGGREGATE_KEYED by a fact: the assertion F that column 0 is a key of X gives
; the lemma F => (= A M), for A the aggregate by column 0 and M a map of X,
; which the rewriter of the theory cannot give
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
