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
(assert (not (rel.acyclic R)))


(check-sat)