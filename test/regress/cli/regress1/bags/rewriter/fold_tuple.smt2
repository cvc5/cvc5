; REQUIRES: unrestricted-mode
; FOLD_TUPLE: a fold of tuples whose components read their own accumulator
; only is the tuple of the folds of the components
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Bag (Tuple Int)))
(define-fun f ((t (Tuple Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 0) t))
         (+ ((_ tuple.select 1) acc) 1)))
(define-fun sum ((t (Tuple Int)) (a Int)) Int (+ a ((_ tuple.select 0) t)))
(define-fun cnt ((t (Tuple Int)) (a Int)) Int (+ a 1))
(assert (not (= (bag.fold f (tuple 0 0) X)
                (tuple (bag.fold sum 0 X) (bag.fold cnt 0 X)))))
(check-sat)
