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
(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (=> (in ?s (inter ?t1 ?t2)) (and (in ?s ?t1) (in ?s ?t2))) :rewrite-rule)))


(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (! (=> (not (in ?s ?t1)) (not (in ?s (inter ?t1 ?t2)))) :pattern ((inter ?t1 ?t2)) ) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (! (=> (not (in ?s ?t2)) (not (in ?s (inter ?t1 ?t2)))) :pattern ((inter ?t1 ?t2)) ) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (=> (and (not (in ?s (inter ?t1 ?t2)))  (in ?s ?t1)) (not (in ?s ?t2))) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (=> (and (not (in ?s (inter ?t1 ?t2)))  (in ?s ?t2)) (not (in ?s ?t1))) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (! (=> (and (in ?s ?t1)  (in ?s ?t2)) (in ?s (inter ?t1 ?t2))) :pattern ((inter ?t1 ?t2)) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;;;
;; union

(declare-fun union (set set)  set)
(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (=> (not (in ?s (union ?t1 ?t2))) (and (not (in ?s ?t1)) (not (in ?s ?t2)))) :rewrite-rule)))


(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (! (=> (in ?s ?t1) (in ?s (union ?t1 ?t2))) :pattern ((union ?t1 ?t2)) ) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (! (=> (in ?s ?t2) (in ?s (union ?t1 ?t2))) :pattern ((union ?t1 ?t2)) ) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (=> (and (in ?s (union ?t1 ?t2))  (not (in ?s ?t1))) (in ?s ?t2)) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (=> (and (in ?s (union ?t1 ?t2))  (not (in ?s ?t2))) (in ?s ?t1)) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (! (=> (and (not (in ?s ?t1))  (not (in ?s ?t2))) (not (in ?s (union ?t1 ?t2)))) :pattern ((union ?t1 ?t2)) ) :rewrite-rule) ))

;;;;;;;;;;;;;;;;
;;sing

(declare-fun sing (elt)  set)
(assert (forall ((?s elt))
                (! (! (=> true (in ?s (sing ?s))) :pattern ((sing ?s)) ) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 elt))
                (! (=> true (=> (in ?s (sing ?t1)) (= ?s ?t1))) :rewrite-rule) ))

(assert (forall ((?s elt) (?t1 elt))
                (! (=> (not (in ?s (sing ?t1))) (not (= ?s ?t1))) :rewrite-rule) ))



;;;;;;;;;;;;;;;;;;;
;; fullfiling
(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (=> (in ?s (union ?t1 ?t2)) (or (in ?s ?t1) (not (in ?s ?t1)))) :rewrite-rule)))

(assert (forall ((?s elt) (?t1 set) (?t2 set))
                (! (! (=> (in ?s ?t1) (or (in ?s ?t2) (not (in ?s ?t2)))) :pattern ((inter ?t1 ?t2))) :rewrite-rule)))

(assert (forall ((?t1 set) (?t2 set)) (! (=> (not (= ?t1 ?t2)) (exists ((?e elt)) (or (and (in ?e ?t1) (not (in ?e ?t2))) (and (not (in ?e ?t1)) (in ?e ?t2))))) :rewrite-rule)))

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
