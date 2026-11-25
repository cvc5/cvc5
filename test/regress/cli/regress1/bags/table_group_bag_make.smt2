; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; table.group of a table of known rows, written out by GROUP_BAG_MAKE, and
; bag.map and bag.fold of an ite, written out by MAP_ITE and FOLD_ITE
(set-logic HO_ALL)
(declare-const x (Tuple Int Int))
(declare-const y (Tuple Int Int))
(declare-const b Bool)
(define-fun A () (Table Int Int)
  (bag.union_disjoint (bag x 1) (ite b (bag y 2) (as bag.empty (Table Int Int)))))
(define-fun kx () Int ((_ tuple.select 0) x))
(define-fun ky () Int ((_ tuple.select 0) y))

; x and two copies of y in one group
(push 1)
(assert (= ((_ table.group 0) A) (bag (bag.union_disjoint (bag x 1) (bag y 2)) 1)))
(check-sat)
(pop 1)

; two groups when the keys differ
(push 1)
(assert b)
(assert (distinct kx ky))
(assert (not (= ((_ table.group 0) A) (bag.union_disjoint (bag (bag x 1) 1) (bag (bag y 2) 1)))))
(check-sat)
(pop 1)

; one group when the keys are equal
(push 1)
(assert b)
(assert (= kx ky))
(assert (not (= ((_ table.group 0) A) (bag (bag.union_disjoint (bag x 1) (bag y 2)) 1))))
(check-sat)
(pop 1)

; y is not in the table
(push 1)
(assert (not b))
(assert (not (= ((_ table.group 0) A) (bag (bag x 1) 1))))
(check-sat)
(pop 1)

; bag.map, bag.fold and bag.filter of an ite
(push 1)
(define-fun key ((t (Tuple Int Int))) Int ((_ tuple.select 0) t))
(define-fun add ((t (Tuple Int Int)) (s Int)) Int (+ ((_ tuple.select 1) t) s))
(define-fun positive ((t (Tuple Int Int))) Bool (> ((_ tuple.select 1) t) 0))
(define-fun B () (Table Int Int) (ite b (bag x 1) (as bag.empty (Table Int Int))))
(assert (not (and (= (bag.map key B) (ite b (bag kx 1) (as bag.empty (Bag Int))))
                  (= (bag.fold add 0 B) (ite b ((_ tuple.select 1) x) 0))
                  (= (bag.filter positive B)
                     (ite (and b (positive x)) (bag x 1) (as bag.empty (Table Int Int)))))))
(check-sat)
(pop 1)
