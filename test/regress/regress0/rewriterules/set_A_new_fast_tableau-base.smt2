;; A new fast tableau-base ... Domenico Cantone et Calogero G.Zarba
(set-logic AUFLIA)
(set-info :status unsat)

;; don't use a datatypes for currently focusing my_in uf
(declare-sort elt 0)
(declare-sort set 0)

(declare-fun my_in (elt set) Bool)

;;;;;;;;;;;;;;;;;;;;
;; inter

(declare-fun inter (set set)  set)
(assert-propagation ((?s elt) (?t1 set) (?t2 set)) () ()
                  ((my_in ?s (inter ?t1 ?t2))) (and (my_in ?s ?t1) (my_in ?s ?t2)))


(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((inter ?t1 ?t2))) () ((not (my_in ?s ?t1))) (not (my_in ?s (inter ?t1 ?t2))) )

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((inter ?t1 ?t2))) () ((not (my_in ?s ?t2))) (not (my_in ?s (inter ?t1 ?t2))) )

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (my_in ?s (inter ?t1 ?t2))) (my_in ?s ?t1)) (not (my_in ?s ?t2)) )

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (my_in ?s (inter ?t1 ?t2))) (my_in ?s ?t2)) (not (my_in ?s ?t1)))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((inter ?t1 ?t2))) () ((my_in ?s ?t1) (my_in ?s ?t2)) (my_in ?s (inter ?t1 ?t2)) )

;;;;;;;;;;;;;;;;;
;; union

(declare-fun my_union (set set)  set)
(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (my_in ?s (my_union ?t1 ?t2)))) (and (not (my_in ?s ?t1)) (not (my_in ?s ?t2))))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((my_union ?t1 ?t2))) () ((my_in ?s ?t1)) (my_in ?s (my_union ?t1 ?t2)))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((my_union ?t1 ?t2))) () ((my_in ?s ?t2)) (my_in ?s (my_union ?t1 ?t2)))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((my_in ?s (my_union ?t1 ?t2)) (not (my_in ?s ?t1))) (my_in ?s ?t2))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((my_in ?s (my_union ?t1 ?t2)) (not (my_in ?s ?t2))) (my_in ?s ?t1))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((my_union ?t1 ?t2))) () ((not (my_in ?s ?t1)) (not (my_in ?s ?t2))) (not (my_in ?s (my_union ?t1 ?t2))))

;;;;;;;;;;;;;;;;;;;;
;; diff

(declare-fun diff (set set)  set)
(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((my_in ?s (diff ?t1 ?t2))) (and (my_in ?s ?t1) (not (my_in ?s ?t2))))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((diff ?t1 ?t2))) () ((not (my_in ?s ?t1))) (not (my_in ?s (diff ?t1 ?t2))) )

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((diff ?t1 ?t2))) () ((my_in ?s ?t2)) (not (my_in ?s (diff ?t1 ?t2))))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (my_in ?s (diff ?t1 ?t2))) (my_in ?s ?t1)) (my_in ?s ?t2))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (my_in ?s (diff ?t1 ?t2))) (not (my_in ?s ?t2))) (not (my_in ?s ?t1)))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((diff ?t1 ?t2))) () ((my_in ?s ?t1) (not (my_in ?s ?t2))) (my_in ?s (diff ?t1 ?t2)) )

;;;;;;;;;;;;;;;;
;;sing

(declare-fun sing (elt)  set)
(assert-propagation ((?s elt))
                   (((sing ?s))) () () (my_in ?s (sing ?s)) )

(assert-propagation ((?s elt) (?t1 elt))
                   () () ((my_in ?s (sing ?t1))) (= ?s ?t1))

(assert-propagation ((?s elt) (?t1 elt))
                   () () ((not (my_in ?s (sing ?t1)))) (not (= ?s ?t1)))

;;;;;;;;;;;;;;;;;;;
;; fullfiling runned at Full effort
(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((my_in ?s (my_union ?t1 ?t2))) (or (my_in ?s ?t1) (not (my_in ?s ?t1))))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((inter ?t1 ?t2))) () ((my_in ?s ?t1)) (or (my_in ?s ?t2) (not (my_in ?s ?t2))))

(assert-propagation ((?t1 set) (?t2 set))
                   () () ((not (= ?t1 ?t2))) (exists ((?e elt)) (or (and (my_in ?e ?t1) (not (my_in ?e ?t2))) (and (not (my_in ?e ?t1)) (my_in ?e ?t2)))))

;;;;;;;;;;;;;;;;;;;
;; shortcut
(declare-fun subset (set set) Bool)
(assert-reduction ((?t1 set) (?t2 set))
                 () () ((subset ?t1 ?t2)) (= (my_union ?t1 ?t2) ?t2))

(declare-fun e () elt)
(declare-fun t1 () set)
(declare-fun t2 () set)
(declare-fun t3 () set)

;;(assert (not (=> (my_in e (inter (my_union t1 t2) (my_union t1 t1))) (my_in e (my_union t1 t1)))))
;;(assert (not (=> (my_in e (my_union t1 t1)) (my_in e t1))))

;; hyp
;;(assert (=> (my_in e (my_union t1 t1)) (my_in e t1)))

;;(assert (not (=> (my_in e (inter (my_union t1 t2) (my_union t1 t1))) (my_in e t1))))

;;(assert (or (and (not (my_in e (my_union t1 (my_union t2 t3)))) (my_in e (my_union (my_union t1 t2) t3))) (and (my_in e (my_union t1 (my_union t2 t3))) (not (my_in e (my_union (my_union t1 t2) t3))))) )
(assert (not (= (my_union t1 (my_union t2 t3)) (my_union (my_union t1 t2) t3))) )

(check-sat)

(exit)
