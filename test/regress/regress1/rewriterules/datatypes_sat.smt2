;; try to solve datatypes with rewriterules
(set-logic AUFLIA)
(set-info :status sat)

;; lists 2 nil
(declare-sort elt 0) ;; we suppose that elt is infinite
(declare-sort list 0)

(declare-fun nil1 () list)
(declare-fun nil2 () list)
(declare-fun cons (elt list) list)

;;;;;;;;;;;;;;;;;;;;
;; injective

(declare-fun inj1 (list) elt)
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (inj1 (cons ?e ?l)) ?e))) :pattern ((cons ?e ?l)) ) :rewrite-rule) ))

(declare-fun inj2 (list) list)
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (inj2 (cons ?e ?l)) ?l))) :pattern ((cons ?e ?l)) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;;;;
;; projection

(declare-fun proj1 (list) elt)
(assert (forall ((?e elt) (?l list))
                (! (= (proj1 (cons ?e ?l)) ?e) :rewrite-rule) ))

(declare-fun proj2 (list) list)
(assert (forall ((?e elt) (?l list))
                (! (= (proj2 (cons ?e ?l)) ?l) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;;;
;; test
(declare-fun iscons (list) Bool)
(assert (= (iscons nil1) false))
(assert (= (iscons nil2) false))
(assert (forall ((?e elt) (?l list))
                (! (! (=> true (=> true (= (iscons (cons ?e ?l)) true))) :pattern ((cons ?e ?l)) ) :rewrite-rule) ))

(assert (forall ((?l list))
                (! (! (=> true (=> (iscons ?l) (= ?l (cons (proj1 ?l) (proj2 ?l))))) :pattern ((proj1 ?l)) ) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (! (=> true (=> (iscons ?l) (= ?l (cons (proj1 ?l) (proj2 ?l))))) :pattern ((proj2 ?l)) ) :rewrite-rule) ))


(declare-fun isnil1 (list) Bool)
(assert (= (isnil1 nil1) true))
(assert (= (isnil1 nil2) false))
(assert (forall ((?e elt) (?l list))
                (! (= (isnil1 (cons ?e ?l)) false) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (=> true (=> (isnil1 ?l) (= ?l nil1))) :rewrite-rule) ))

(declare-fun isnil2 (list) Bool)
(assert (= (isnil2 nil1) false))
(assert (= (isnil2 nil2) true))
(assert (forall ((?e elt) (?l list))
                (! (= (isnil2 (cons ?e ?l)) false) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (=> true (=> (isnil2 ?l) (= ?l nil2))) :rewrite-rule) ))

;; distinct
(assert (forall ((?l list))
                (! (=> (isnil1 ?l) (and (not (isnil2 ?l)) (not (iscons ?l))) ) :rewrite-rule) ))

(assert (forall ((?l list))
                (! (=> (isnil2 ?l) (and (not (isnil1 ?l)) (not (iscons ?l))) ) :rewrite-rule) ))

(assert (forall ((?l list))
                (! (=> (iscons ?l) (and (not (isnil1 ?l)) (not (isnil2 ?l))) ) :rewrite-rule) ))


;;;;;;;;;;;;;;;;;;;
;; case-split
(assert (forall ((?l list))
                (! (! (=> true (or (isnil1 ?l) (isnil2 ?l) (iscons ?l))) :pattern ((proj1 ?l)) ) :rewrite-rule) ))
(assert (forall ((?l list))
                (! (! (=> true (or (isnil1 ?l) (isnil2 ?l) (iscons ?l))) :pattern ((proj2 ?l)) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;;;
;; finite case-split
(assert (forall ((?l list))
                 (! (=> (not (iscons ?l)) (or (isnil1 ?l) (isnil2 ?l))) :rewrite-rule) ))



;;;;; goal

(declare-fun e () elt)
(declare-fun l1 () list)
(declare-fun l2 () list)


(assert (not (=> (iscons l1) (=> (= (proj2 l1) (proj2 l2)) (= l1 (cons (proj1 l2) (proj2 l2)))))))

(check-sat)

(exit)
