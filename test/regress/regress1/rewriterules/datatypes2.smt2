;; try to solve datatypes with rewriterules
(set-logic AUFLIA)
(set-info :status unsat)

;; lists 2 nil
(declare-sort elt 0) ;; we suppose that elt is infinite
(declare-sort list 0)

(declare-fun nil1 () list)
(declare-fun nil2 () list)
(declare-fun cons1 (elt list) list)
(declare-fun cons2 (elt list) list)

;;;;;;;;;;;;;;;;;;;;
;; injective

(declare-fun inj11 (list) elt)
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (inj11 (cons1 ?e ?l)) ?e))) :pattern ((cons1 ?e ?l)) ) :rewrite-rule) ))

(declare-fun inj12 (list) list)
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (inj12 (cons1 ?e ?l)) ?l))) :pattern ((cons1 ?e ?l)) ) :rewrite-rule) ))

(declare-fun inj21 (list) elt)
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (inj21 (cons2 ?e ?l)) ?e))) :pattern ((cons2 ?e ?l)) ) :rewrite-rule) ))

(declare-fun inj22 (list) list)
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (inj22 (cons2 ?e ?l)) ?l))) :pattern ((cons2 ?e ?l)) ) :rewrite-rule) ))


;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun proj11 (list) elt)
(assert (forall ((?e elt) (?l list))
                (! (= (proj11 (cons1 ?e ?l)) ?e) :rewrite-rule) ))

(declare-fun proj12 (list) list)
(assert (forall ((?e elt) (?l list))
                (! (= (proj12 (cons1 ?e ?l)) ?l) :rewrite-rule) ))


(declare-fun proj21 (list) elt)
(assert (forall ((?e elt) (?l list))
                (! (= (proj21 (cons2 ?e ?l)) ?e) :rewrite-rule) ))

(declare-fun proj22 (list) list)
(assert (forall ((?e elt) (?l list))
                (! (= (proj22 (cons2 ?e ?l)) ?l) :rewrite-rule) ))


;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun iscons1 (list) Bool)
(assert (= (iscons1 nil1) false))
(assert (= (iscons1 nil2) false))
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (iscons1 (cons1 ?e ?l)) true))) :pattern ((cons1 ?e ?l)) ) :rewrite-rule) ))
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (iscons1 (cons2 ?e ?l)) false))) :pattern ((cons2 ?e ?l)) ) :rewrite-rule) ))

(assert (forall ((?l list))
                (! (! (=> true (=> (iscons1 ?l) (= ?l (cons1 (proj11 ?l) (proj12 ?l))))) :pattern ((proj11 ?l)) ) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (! (=> true (=> (iscons1 ?l) (= ?l (cons1 (proj11 ?l) (proj12 ?l))))) :pattern ((proj12 ?l)) ) :rewrite-rule) ))


(declare-fun iscons2 (list) Bool)
(assert (= (iscons2 nil1) false))
(assert (= (iscons2 nil2) false))
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (iscons2 (cons1 ?e ?l)) false))) :pattern ((cons1 ?e ?l)) ) :rewrite-rule) ))
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (iscons2 (cons2 ?e ?l)) true))) :pattern ((cons2 ?e ?l)) ) :rewrite-rule) ))

(assert (forall ((?l list))
                (! (! (=> true (=> (iscons2 ?l) (= ?l (cons2 (proj21 ?l) (proj22 ?l))))) :pattern ((proj21 ?l)) ) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (! (=> true (=> (iscons2 ?l) (= ?l (cons2 (proj21 ?l) (proj22 ?l))))) :pattern ((proj22 ?l)) ) :rewrite-rule) ))


(declare-fun isnil1 (list) Bool)
(assert (= (isnil1 nil1) true))
(assert (= (isnil1 nil2) false))
(assert (forall ((?e elt) (?l list))
                (! (= (isnil1 (cons1 ?e ?l)) false) :rewrite-rule) ))
(assert (forall ((?e elt) (?l list))
                (! (= (isnil1 (cons2 ?e ?l)) false) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (=> true (=> (isnil1 ?l) (= ?l nil1))) :rewrite-rule) ))

(declare-fun isnil2 (list) Bool)
(assert (= (isnil2 nil1) false))
(assert (= (isnil2 nil2) true))
(assert (forall ((?e elt) (?l list))
                (! (= (isnil2 (cons1 ?e ?l)) false) :rewrite-rule) ))
(assert (forall ((?e elt) (?l list))
                (! (= (isnil2 (cons2 ?e ?l)) false) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (=> true (=> (isnil2 ?l) (= ?l nil2))) :rewrite-rule) ))

;; distinct
(assert (forall ((?l list))
                (! (=> (isnil1 ?l) (and (not (isnil2 ?l)) (not (iscons1 ?l)) (not (iscons2 ?l))) ) :rewrite-rule) ))

(assert (forall ((?l list))
                (! (=> (isnil2 ?l) (and (not (isnil1 ?l)) (not (iscons1 ?l)) (not (iscons2 ?l))) ) :rewrite-rule) ))

(assert (forall ((?l list))
                (! (=> (iscons1 ?l) (and (not (isnil1 ?l)) (not (isnil2 ?l)) (not (iscons2 ?l))) ) :rewrite-rule) ))

(assert (forall ((?l list))
                (! (=> (iscons2 ?l) (and (not (isnil1 ?l)) (not (isnil2 ?l)) (not (iscons1 ?l))) ) :rewrite-rule) ))


;;;;;;;;;;;;;;;;;;;
;; case-split
(assert (forall ((?l list))
                (! (! (=> true (or (isnil1 ?l) (isnil2 ?l) (iscons1 ?l) (iscons2 ?l))) :pattern ((proj11 ?l)) ) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (! (=> true (or (isnil1 ?l) (isnil2 ?l) (iscons1 ?l) (iscons2 ?l))) :pattern ((proj12 ?l)) ) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (! (=> true (or (isnil1 ?l) (isnil2 ?l) (iscons1 ?l) (iscons2 ?l))) :pattern ((proj21 ?l)) ) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (! (=> true (or (isnil1 ?l) (isnil2 ?l) (iscons1 ?l) (iscons2 ?l))) :pattern ((proj22 ?l)) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;;;
;; finite case-split
(assert (forall ((?l list))
                 (! (=> (and (not (iscons1 ?l)) (not (iscons2 ?l))) (or (isnil1 ?l) (isnil2 ?l))) :rewrite-rule) ))



;;;;; goal

(declare-fun e () elt)
(declare-fun l1 () list)
(declare-fun l2 () list)


 (assert (not (=> (iscons2 l1) (=> (= (proj22 l1) (proj22 l2)) (= l1 (cons2 (proj21 l1) (proj22 l2)))))))

;;(assert (= (cons1 l1 l2) (cons2 l1 l2)))

(check-sat)

(exit)
