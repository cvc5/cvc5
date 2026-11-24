; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; table.aggr of a table of known rows, reduced by AGGREGATE_BAG_MAKE to
; bag.map, table.group and bag.fold, which GROUP_BAG_MAKE, MAP_ITE and FOLD_ITE
; write out:
;   SELECT k, COUNT(*) FROM A GROUP BY k
(set-logic HO_ALL)
(declare-const x (Tuple Int Int))
(declare-const y (Tuple Int Int))
(define-fun count ((A (Table Int Int))) (Table Int Int)
  ((_ table.aggr 0)
   (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
     (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
   (tuple 0 0)
   A))
(define-fun A () (Table Int Int) (bag.union_disjoint (bag x 1) (bag y 1)))
(define-fun kx () Int ((_ tuple.select 0) x))
(define-fun ky () Int ((_ tuple.select 0) y))

; x and y in one group
(push 1)
(assert (= (count A) (bag (tuple kx 2) 1)))
(check-sat)
(pop 1)

; two groups when the keys differ
(push 1)
(assert (distinct kx ky))
(assert (not (= (count A) (bag.union_disjoint (bag (tuple kx 1) 1) (bag (tuple ky 1) 1)))))
(check-sat)
(pop 1)

; the rows of a filter: y is not in it
(push 1)
(define-fun nonNegative ((t (Tuple Int Int))) Bool (>= ((_ tuple.select 1) t) 0))
(assert (nonNegative x))
(assert (not (nonNegative y)))
(assert (not (= (count (bag.filter nonNegative A)) (bag (tuple kx 1) 1))))
(check-sat)
(pop 1)

; a row with two copies is folded twice
(push 1)
(assert (not (= (count (bag x 2)) (bag (tuple kx 2) 1))))
(check-sat)
(pop 1)

; the rows of a filter of an ite: x is in the table if b, y is filtered out
(push 1)
(declare-const b Bool)
(define-fun nonNegative ((t (Tuple Int Int))) Bool (>= ((_ tuple.select 1) t) 0))
(assert (nonNegative x))
(assert (not (nonNegative y)))
(assert (not (= (count (bag.filter nonNegative (ite b A (bag y 1))))
                (ite b (bag (tuple kx 1) 1) (as bag.empty (Table Int Int))))))
(check-sat)
(pop 1)
