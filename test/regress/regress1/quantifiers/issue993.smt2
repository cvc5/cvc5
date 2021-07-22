(set-logic AUFBVDTNIRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-sort us_private 0)

(declare-sort integer 0)

(declare-fun to_rep1 (integer) Int)

(declare-datatypes ((us_split_fields 0)) (((mk___split_fields (rec__unit1__t1__c1 integer) (rec__ext__ us_private)))))
(declare-datatypes ((us_split_fields__ref 0)) (((mk___split_fields__ref (us_split_fields__content us_split_fields)))))

(define-fun us_split_fields__ref___projection ((a us_split_fields__ref)) us_split_fields 
  (us_split_fields__content a))

(declare-datatypes ((us_rep 0)) (((mk___rep (us_split_fields1 us_split_fields) (attr__tag Int)))))
(define-fun us_rep___projection ((a us_rep)) us_split_fields (us_split_fields1
                                                             a))

(declare-fun is_zero (us_rep) Bool)

(declare-fun is_zero__post_predicate (Bool us_rep) Bool)

;; is_zero__def_axiom
  (assert
  (forall ((x us_rep))
  (! (=> (is_zero__post_predicate (is_zero x) x)
     (= (= (is_zero x) true)
     (= (to_rep1 (rec__unit1__t1__c1 (us_split_fields1 x))) 0))) :pattern (
  (is_zero x)) )))

(declare-datatypes ((us_split_fields2 0)) (((mk___split_fields1 (rec__unit2__t2__c2 integer) (rec__unit1__t1__c11 integer) (rec__ext__1 us_private)))))
(declare-datatypes ((us_split_fields__ref1 0)) (((mk___split_fields__ref1 (us_split_fields__content1 us_split_fields2)))))

(define-fun us_split_fields__ref_2__projection ((a us_split_fields__ref1)) us_split_fields2 
  (us_split_fields__content1 a))

(declare-datatypes ((us_rep1 0)) (((mk___rep1 (us_split_fields3 us_split_fields2) (attr__tag1 Int)))))
(define-fun us_rep_3__projection ((a us_rep1)) us_split_fields2 (us_split_fields3
                                                                a))

(declare-fun hide_ext__ (integer us_private) us_private)

(define-fun to_base ((a us_rep1)) us_rep (mk___rep
                                         (mk___split_fields
                                         (rec__unit1__t1__c11
                                         (us_split_fields3 a))
                                         (hide_ext__
                                         (rec__unit2__t2__c2
                                         (us_split_fields3 a))
                                         (rec__ext__1 (us_split_fields3 a))))
                                         (attr__tag1 a)))

(declare-fun is_zero2 (us_rep1) Bool)

(declare-fun is_zero__post_predicate2 (Bool us_rep1) Bool)

;; is_zero__def_axiom
  (assert
  (forall ((x us_rep1))
  (! (=> (is_zero__post_predicate2 (is_zero2 x) x)
     (= (= (is_zero2 x) true)
     (and (= (is_zero (to_base x)) true)
     (= (to_rep1 (rec__unit2__t2__c2 (us_split_fields3 x))) 0)))) :pattern (
  (is_zero2 x)) )))

(declare-fun x2__attr__tag () Int)

(declare-fun x2__split_fields () integer)

(declare-fun x2__split_fields1 () integer)

(declare-fun x2__split_fields2 () us_private)

;; H
  (assert
  (forall ((x2__split_fields3 us_split_fields2)) (is_zero__post_predicate2
  (is_zero2 (mk___rep1 x2__split_fields3 x2__attr__tag))
  (mk___rep1 x2__split_fields3 x2__attr__tag))))

;; H
  (assert
  (and (= (to_rep1 x2__split_fields1) 0) (= (to_rep1 x2__split_fields) 0)))

;; Should be enough to imply following hypothesis
  (assert
  (forall ((x us_rep1)) (is_zero__post_predicate (is_zero (to_base x))
  (to_base x))))

(assert
;; WP_parameter_def
 ;; File "main.adb", line 5, characters 0-0
  (not
   (= (is_zero (to_base (mk___rep1
     (mk___split_fields1 x2__split_fields x2__split_fields1
    x2__split_fields2) x2__attr__tag))) true)))
(check-sat)
