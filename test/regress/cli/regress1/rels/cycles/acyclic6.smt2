(set-logic ALL)
;; (set-info :status sat)
(set-option :rels-exp true)
(set-option :produce-unsat-cores true)
; Test cycle rules


(declare-fun R () (Set (Tuple Int Int))) 
(declare-fun a () Int)
(declare-fun b () Int)


(declare-fun iden () (Set (Tuple Int Int)))


(assert (forall ((a Int) (b Int)) (and 
  (=> (set.member (tuple a b) iden) (= a b))
  (=> (= a b) (set.member (tuple a b) iden))
  )))


(define-fun irreflexive ((r (Set (Tuple Int Int)))) Bool 
  (= (set.inter r iden) (as set.empty (Set (Tuple Int Int))))
 )


(assert (irreflexive (rel.tclosure R)))


; irreflexive (rel.tclosure R)
; not acyclic R
; update unroll cycle to do tclosure membership


;; (assert (distinct a b))
;; (assert (= R (set.singleton (tuple a b))))
;; (assert (set.member (tuple a b) R))
;; (assert (not (rel.acyclic (rel.tclosure R))))
(assert (not (rel.acyclic R)))
;; (assert (rel.acyclic R))


(check-sat)
(get-unsat-core)




;; (set-logic ALL)
;; (set-info :status unsat)
;; (set-option :rels-exp true)
;; ; Test cycle rules


;; (declare-fun R () (Set (Tuple Int Int))) 
;; (declare-fun x () Int)


;; (assert (rel.acyclic R))
;; (assert (set.member (tuple x x) R))


;; (check-sat)
