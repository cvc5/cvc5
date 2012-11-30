;; Back to the Future ... Shuvendu K.Lhiri, Shaz Qadeer
(set-logic AUFLIA)
(set-info :status unsat)

(declare-sort elt 0)

(declare-fun f (elt) elt)
(declare-fun Rf (elt elt elt) Bool)

;;eq
(assert-propagation ((?x elt)) ((?x)) () () (or (= ?x ?x) (not (= ?x ?x))) )
;; reflexive
(assert-propagation ((?x elt)) ((?x)) () () (Rf ?x ?x ?x) )
;; step
(assert-propagation ((?x elt)) (((f ?x))) () () (Rf ?x (f ?x) (f ?x)) )
;; reach
(assert-propagation ((?x1 elt)(?x2 elt)) (((f ?x1))) () ((Rf ?x1 ?x2 ?x2)) (or (= ?x1 ?x2) (Rf ?x1 (f ?x1) ?x2)) )
;; cycle
(assert-propagation ((?x1 elt)(?x2 elt)) (((f ?x1))) ((= (f ?x1) ?x1)) ((Rf ?x1 ?x2 ?x2)) (= ?x1 ?x2) )
;; sandwich
(assert-propagation ((?x1 elt)(?x2 elt)) () () ((Rf ?x1 ?x2 ?x1)) (= ?x1 ?x2) )
;; order1
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () () ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))
                    (or (Rf ?x1 ?x2 ?x3) (Rf ?x1 ?x3 ?x2)) )
;; order2
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () () ((Rf ?x1 ?x2 ?x3))
                    (and (Rf ?x1 ?x2 ?x2) (Rf ?x2 ?x3 ?x3)) )
;; transitive1
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () () ((Rf ?x1 ?x2 ?x2)(Rf ?x2 ?x3 ?x3))
                    (Rf ?x1 ?x3 ?x3) )
;; transitive2
(assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () () ((Rf ?x0 ?x1 ?x2)(Rf ?x1 ?x3 ?x2))
                    (and (Rf ?x0 ?x1 ?x3) (Rf ?x0 ?x3 ?x2)) )
;;transitive3
(assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () () ((Rf ?x0 ?x1 ?x2)(Rf ?x0 ?x3 ?x1))
                    (and (Rf ?x0 ?x3 ?x2) (Rf ?x3 ?x1 ?x2)) )

(declare-fun e1 () elt)
(declare-fun e2 () elt)
(declare-fun e3 () elt)
(declare-fun e4 () elt)


;; (assert (=> (Rf e1 e2 e3) (Rf e1 (f e1) (f e1)) ))

;; (assert (=> (Rf e1 e2 e3) (Rf e1 e3 e3) ))

;; (assert (=> (Rf e1 e2 e3) (or (= e1 e3) (Rf e1 (f e1) e3)) ))

(assert (not (=> (and (not (= e1 e2)) (Rf e1 e2 e3)) (Rf e1 (f e1) e3) )))


(check-sat)
(exit)