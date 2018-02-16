;; A new fast tableau-base ... Domenico Cantone et Calogero G.Zarba
(set-logic AUFLIA)
(set-info :status unsat)

;; don't use a datatypes for currently focusing in uf
(declare-sort elt 0)
(declare-sort set 0)

(declare-fun in (elt set) Bool)

;;;;;;;;;;;;;;;;;;;;
;; inter

(declare-fun inter (set set)  set)
(assert-propagation ((?s elt) (?t1 set) (?t2 set)) () ()
                  ((in ?s (inter ?t1 ?t2))) (and (in ?s ?t1) (in ?s ?t2)))


(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((inter ?t1 ?t2))) () ((not (in ?s ?t1))) (not (in ?s (inter ?t1 ?t2))) )

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((inter ?t1 ?t2))) () ((not (in ?s ?t2))) (not (in ?s (inter ?t1 ?t2))) )

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (in ?s (inter ?t1 ?t2))) (in ?s ?t1)) (not (in ?s ?t2)) )

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (in ?s (inter ?t1 ?t2))) (in ?s ?t2)) (not (in ?s ?t1)))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((inter ?t1 ?t2))) () ((in ?s ?t1) (in ?s ?t2)) (in ?s (inter ?t1 ?t2)) )

;;;;;;;;;;;;;;;;;
;; union

(declare-fun union (set set)  set)
(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (in ?s (union ?t1 ?t2)))) (and (not (in ?s ?t1)) (not (in ?s ?t2))))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((union ?t1 ?t2))) () ((in ?s ?t1)) (in ?s (union ?t1 ?t2)))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((union ?t1 ?t2))) () ((in ?s ?t2)) (in ?s (union ?t1 ?t2)))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((in ?s (union ?t1 ?t2)) (not (in ?s ?t1))) (in ?s ?t2))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((in ?s (union ?t1 ?t2)) (not (in ?s ?t2))) (in ?s ?t1))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((union ?t1 ?t2))) () ((not (in ?s ?t1)) (not (in ?s ?t2))) (not (in ?s (union ?t1 ?t2))))

;;;;;;;;;;;;;;;;;;;;
;; diff

(declare-fun diff (set set)  set)
(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((in ?s (diff ?t1 ?t2))) (and (in ?s ?t1) (not (in ?s ?t2))))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((diff ?t1 ?t2))) () ((not (in ?s ?t1))) (not (in ?s (diff ?t1 ?t2))) )

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((diff ?t1 ?t2))) () ((in ?s ?t2)) (not (in ?s (diff ?t1 ?t2))))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (in ?s (diff ?t1 ?t2))) (in ?s ?t1)) (in ?s ?t2))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((not (in ?s (diff ?t1 ?t2))) (not (in ?s ?t2))) (not (in ?s ?t1)))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((diff ?t1 ?t2))) () ((in ?s ?t1) (not (in ?s ?t2))) (in ?s (diff ?t1 ?t2)) )

;;;;;;;;;;;;;;;;
;;sing

(declare-fun sing (elt)  set)
(assert-propagation ((?s elt))
                   (((sing ?s))) () () (in ?s (sing ?s)) )

(assert-propagation ((?s elt) (?t1 elt))
                   () () ((in ?s (sing ?t1))) (= ?s ?t1))

(assert-propagation ((?s elt) (?t1 elt))
                   () () ((not (in ?s (sing ?t1)))) (not (= ?s ?t1)))

;;;;;;;;;;;;;;;;;;;
;; fullfiling runned at Full effort
(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   () () ((in ?s (union ?t1 ?t2))) (or (in ?s ?t1) (not (in ?s ?t1))))

(assert-propagation ((?s elt) (?t1 set) (?t2 set))
                   (((inter ?t1 ?t2))) () ((in ?s ?t1)) (or (in ?s ?t2) (not (in ?s ?t2))))

(assert-propagation ((?t1 set) (?t2 set))
                   () () ((not (= ?t1 ?t2))) (exists ((?e elt)) (or (and (in ?e ?t1) (not (in ?e ?t2))) (and (not (in ?e ?t1)) (in ?e ?t2)))))

;;;;;;;;;;;;;;;;;;;
;; shortcut
(declare-fun subset (set set) Bool)
(assert-reduction ((?t1 set) (?t2 set))
                 () () ((subset ?t1 ?t2)) (= (union ?t1 ?t2) ?t2))

(declare-fun e () elt)
(declare-fun t1 () set)
(declare-fun t2 () set)
(declare-fun t3 () set)

;;(assert (not (=> (in e (inter (union t1 t2) (union t1 t1))) (in e (union t1 t1)))))
;;(assert (not (=> (in e (union t1 t1)) (in e t1))))

;; hyp
;;(assert (=> (in e (union t1 t1)) (in e t1)))

;;(assert (not (=> (in e (inter (union t1 t2) (union t1 t1))) (in e t1))))

;;(assert (or (and (not (in e (union t1 (union t2 t3)))) (in e (union (union t1 t2) t3))) (and (in e (union t1 (union t2 t3))) (not (in e (union (union t1 t2) t3))))) )
(assert (not (= (union t1 (union t2 t3)) (union (union t1 t2) t3))) )

(check-sat)

(exit)
