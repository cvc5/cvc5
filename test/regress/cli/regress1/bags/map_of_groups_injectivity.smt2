; REQUIRES: unrestricted-mode
; The aggregate reduces to a map over the groups of X whose function folds a
; group. Whether that function is injective is not asked of a subsolver,
; which would unroll the folds and not return.
(set-logic HO_ALL)
(set-info :status sat)
(declare-const X (Bag (Tuple Int Int)))
; COUNT(*) by column 0
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int))) (Tuple Int)
  (tuple (+ ((_ tuple.select 0) acc) 1)))
(assert (not (= ((_ table.aggr 0) f (tuple 0) X)
                (bag.map (lambda ((t (Tuple Int Int))) (tuple 1)) X))))
(check-sat)
