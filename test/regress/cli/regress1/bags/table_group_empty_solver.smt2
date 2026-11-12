; REQUIRES: unrestricted-mode
; CPC checking fails because the signature does not define table.aggr.
; DISABLE-TESTER: cpc
; COMMAND-LINE: --simplification=none
; As table_group_empty.smt2, through the solver: without simplification, X is
; not replaced by the empty table.
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const X (Table Int Int))
; k, SUM(v) by k
(define-fun f ((t (Tuple Int Int)) (acc (Tuple Int Int))) (Tuple Int Int)
  (tuple ((_ tuple.select 0) t)
         (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
(assert (= X (as bag.empty (Table Int Int))))
(assert
 (or (not (= ((_ table.group 0) X) (as bag.empty (Bag (Table Int Int)))))
     (not (= ((_ table.aggr 0) f (tuple 0 0) X) (as bag.empty (Table Int Int))))))
(check-sat)
