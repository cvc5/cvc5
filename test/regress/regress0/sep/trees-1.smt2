(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)

(declare-sort Loc 0)
(declare-const loc0 Loc)

(declare-datatypes ((Node 0)) (((node (data Int) (left Loc) (right Loc)))))
(declare-heap (Loc Node))

(declare-fun data0 () Node)

(declare-const dv Int)
(declare-const v Loc)

(declare-const dl Int)
(declare-const l Loc)
(declare-const dr Int)
(declare-const r Loc)

(define-fun ten-tree0 ((x Loc) (d Int)) Bool 
(or (and (_ emp Loc Node) (= x (as sep.nil Loc))) (and (sep (pto x (node d l r)) (and (_ emp Loc Node) (= l (as sep.nil Loc))) (and (_ emp Loc Node) (= r (as sep.nil Loc)))) (= dl (- d 10)) (= dr (+ d 10)))))

(declare-const dy Int)
(declare-const y Loc)
(declare-const dz Int)
(declare-const z Loc)

(define-fun ord-tree0 ((x Loc) (d Int)) Bool 
(or (and (_ emp Loc Node) (= x (as sep.nil Loc))) (and (sep (pto x (node d y z)) (and (_ emp Loc Node) (= y (as sep.nil Loc))) (and (_ emp Loc Node) (= z (as sep.nil Loc)))) (<= dy d) (<= d dz))))

;------- f -------
(assert (= y (as sep.nil Loc)))
(assert (= z (as sep.nil Loc)))

(assert (= dy dv))
(assert (= dz (+ dv 10)))
;-----------------

(assert (not (= v (as sep.nil Loc))))

(assert (ten-tree0 v dv))
(assert (not (ord-tree0 v dv)))

(check-sat)
