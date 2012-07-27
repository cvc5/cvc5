;; Back to the Future ... Shuvendu K.Lhiri, Shaz Qadeer
(set-logic AUFLIA)
(set-info :status unsat)

(declare-sort elt 0)

(declare-fun f (elt) elt)
(declare-fun Rf (elt elt elt) Bool)

;; reflexive
;;(assert-propagation ((?x elt)) () () (Rf ?x ?x ?x) ((?x)) )
;; step
(assert-propagation ((?x elt)) () () (Rf ?x (f ?x) (f ?x)) (((f ?x))) )
;; (assert-propagation ((?x elt)) () () (Rf ?x (f ?x) (f ?x)) (((Rf ?x (f ?x) (f ?x)))) )
;; (assert-propagation ((?x elt)) () () (=> true (Rf ?x (f ?x) (f ?x))) (((f ?x))) )

;; reach
(assert-propagation ((?x1 elt)(?x2 elt)) () ((Rf ?x1 ?x2 ?x2)) (or (= ?x1 ?x2) (Rf ?x1 (f ?x1) ?x2)) (((f ?x1))) )
;; ;; reach extended
;; (assert-propagation ((?x1 elt)(?x2 elt)) ((not (= ?x1 ?x2))(Rf ?x1 ?x2 ?x2)) () (Rf ?x1 (f ?x1) ?x2) (((Rf ?x1 (f ?x1) ?x2))) )
;; ;; reach extended
;; (assert-propagation ((?x1 elt)(?x2 elt)) ((not (Rf ?x1 (f ?x1) ?x2))(Rf ?x1 ?x2 ?x2)) () (= ?x1 ?x2) (((Rf ?x1 (f ?x1) ?x2))) )

;; cycle
(assert-propagation ((?x1 elt)(?x2 elt)) ((= (f ?x1) ?x1)) ((Rf ?x1 ?x2 ?x2)) (= ?x1 ?x2) (((f ?x1))) )
;; (assert-propagation ((?x1 elt)(?x2 elt)) ((= (f ?x1) ?x1)) ((Rf ?x1 ?x2 ?x2)) (= ?x1 ?x2) () )

;; (assert-propagation ((?x1 elt)(?x2 elt)) () () (=> (and (= (f ?x1) ?x1) (Rf ?x1 ?x2 ?x2)) (= ?x1 ?x2)) (((Rf ?x1 ?x2 ?x2)(f ?x1))) )

;; sandwich
(assert-propagation ((?x1 elt)(?x2 elt)) () ((Rf ?x1 ?x2 ?x1)) (= ?x1 ?x2) () )
;; (assert-propagation ((?x1 elt)(?x2 elt)) () () (=> (Rf ?x1 ?x2 ?x1) (= ?x1 ?x2)) (((Rf ?x1 ?x2 ?x1))) )

;; order1
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ()
                    ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)) (or (Rf ?x1 ?x2 ?x3) (Rf ?x1 ?x3 ?x2)) () )

;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ()
;;                     (=> (and (Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)) (or (Rf ?x1 ?x2 ?x3) (Rf ?x1 ?x3 ?x2))) (((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))) )

;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
;;                     (Rf ?x1 ?x2 ?x3) (((Rf ?x1 ?x2 ?x3))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
;;                     (Rf ?x1 ?x3 ?x2) (((Rf ?x1 ?x3 ?x2))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
;;                     (Rf ?x1 ?x2 ?x3) (((Rf ?x1 ?x3 ?x2))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
;;                     (Rf ?x1 ?x3 ?x2) (((Rf ?x1 ?x2 ?x3))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
;;                     (Rf ?x1 ?x2 ?x3) (((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
;;                     (Rf ?x1 ?x3 ?x2) (((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))) )

;; order2
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x1 ?x2 ?x3))
                    (and (Rf ?x1 ?x2 ?x2) (Rf ?x2 ?x3 ?x3)) () )
;; transitive1
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x1 ?x2 ?x2)(Rf ?x2 ?x3 ?x3))
                    (Rf ?x1 ?x3 ?x3) () )
;; ;; transitive1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ((not (Rf ?x1 ?x3 ?x3))(Rf ?x2 ?x3 ?x3))
;;                     (not (Rf ?x1 ?x2 ?x2)) () )
;; ;; transitive1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x1 ?x2 ?x2)(not (Rf ?x1 ?x3 ?x3)))
;;                     (not (Rf ?x2 ?x3 ?x3)) () )

;;transitive2
(assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x0 ?x1 ?x2)(Rf ?x1 ?x3 ?x2))
                    (and (Rf ?x0 ?x1 ?x3) (Rf ?x0 ?x3 ?x2)) () )

;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ()
;;                     (=> (and (Rf ?x0 ?x1 ?x2)(Rf ?x1 ?x3 ?x2))
;;                         (and (Rf ?x0 ?x1 ?x3) (Rf ?x0 ?x3 ?x2)))
;;                     (((Rf ?x0 ?x1 ?x2)(Rf ?x1 ?x3 ?x2))) )

;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((not (Rf ?x0 ?x1 ?x3))(Rf ?x1 ?x3 ?x2))
;;                     (not (Rf ?x0 ?x1 ?x2)) (((Rf ?x0 ?x1 ?x2))) )
;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x0 ?x1 ?x2)(not (Rf ?x0 ?x1 ?x3)))
;;                     (not (Rf ?x1 ?x3 ?x2)) (((Rf ?x1 ?x3 ?x2))) )
;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((not (Rf ?x0 ?x3 ?x2))(Rf ?x1 ?x3 ?x2))
;;                     (not (Rf ?x0 ?x1 ?x2)) (((Rf ?x0 ?x1 ?x2))) )
;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x0 ?x1 ?x2)(not (Rf ?x0 ?x3 ?x2)))
;;                     (not (Rf ?x1 ?x3 ?x2)) (((Rf ?x1 ?x3 ?x2))) )

;; ;;transitive3
(assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x0 ?x1 ?x2)(Rf ?x0 ?x3 ?x1))
                    (and (Rf ?x0 ?x3 ?x2) (Rf ?x3 ?x1 ?x2)) () )

;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ()
;;                     (=> (and (Rf ?x0 ?x1 ?x2)(Rf ?x0 ?x3 ?x1))
;;                         (and (Rf ?x0 ?x3 ?x2) (Rf ?x3 ?x1 ?x2))) (((Rf ?x0 ?x1 ?x2)(Rf ?x0 ?x3 ?x1))) )


(declare-fun e1 () elt)
(declare-fun e2 () elt)
(declare-fun e3 () elt)
(declare-fun e4 () elt)


;;Example0
;;(assert (not (=> (and (not (= e1 e2)) (Rf e1 e2 e3)) (Rf e1 (f e1) e3))) )

;;Thomas' example1 x,e1 y,e2 z,e3 y',e4
;;(assert (not (=> (and (Rf e1 e2 e3) (not (= e2 e3)) (= e4 (f e2))) (Rf e1 e4 e3))))

(declare-fun Rf_avoid (elt elt elt) Bool)

;; (assert-rewrite ((?x0 elt)(?x1 elt)(?exc elt)) () (Rf_avoid ?x0 ?x1 ?exc)
;;                  (or (Rf ?x0 ?x1 ?exc) (and (Rf ?x0 ?x1 ?x1) (not (Rf ?x0 ?exc ?exc)))) () )

(declare-fun null () elt)
(assert (= (f null) null))

(declare-fun join (elt elt) elt)

;; (assert-propagation ((?x elt)(?y elt)(?z elt)) () ((Rf ?x ?z ?z)(Rf ?y ?z ?z)) (Rf ?x (join ?x ?y) ?z) (((join ?x ?y))) )
;; (assert-propagation ((?x elt)(?y elt)) () () (or (and (Rf ?x (join ?x ?y) (join ?x ?y)) (Rf ?y (join ?x ?y) (join ?x ?y))) (= (join ?x ?y) null))  (((join ?x ?y))) )

;;Thomas' example2
;; (assert (not (=> (and (Rf e1 null null) (= (join e1 e2) null)
;; ;; (next' == upd(next, e, e1)
;; )
;; ;; (reach(next', e1, null) )
;; (or (and (Rf e1 null null) (Rf_avoid e1 null e2) )
;;     (and (not (= e2 null)) (Rf_avoid e1 e2 null) (Rf e1 null e2) (Rf_avoid e1 null e2) )
;;     (and (not (= e2 null)) (Rf_avoid e1 e2 null) (Rf e1 null null) (Rf_avoid e1 null e2) ) )
;; )))


;;Thomas' example3
;; join(next, first, e) == null &&
;; reach(next, e, null) &&
;; e != null &&
;; next' == upd(next, e, first) &&
;; first' == e &&
;; e' == sel (next, e)
;; ==>
;; join(next', first', e') == null 


;;Thomas' example3
(assert(not
        (=>
         (and
          ;; (= (join e1 e2) null)
          (Rf e2 null null)
          (not (= e2 null)))
         ;; (next' == upd(next, e2, e1)
         ;;join(next',e1,e2) == null
(or (and (not (Rf (f e2) e2 e2)) (not (Rf e1 e2 e2) ))
;;    (and (Rf (f e2) e2 e2) (not (Rf e1 e1 e1) ))
    (and (Rf e1 e2 e2) (not (Rf (f e2) e1 e1)) )
)
;; (or
;;  (and (not (Rf e1 e2 e2)) (not (Rf e2 e2 e2)))
;;  (and (Rf e1 e2 e2) (not (Rf e2 e1 e1)))
;;  (and (Rf e2 e2 e2) (not (Rf e1 e1 e1)))
;; )
)))



;; ;;Thomas' example wrong sat?
;; (assert (not (=> (and
;;                   (= (join e1 e2) null)
;;                   (Rf e2 null null) (not (= e2 null)))
;; ;; (next' == upd(next, e2, e1)
;; ;;join(next',e1,e2) == null
;; (not (Rf e2 e2 e2))
;; ;; (or
;; ;;  (and (not (Rf e1 e2 e2)) (not (Rf e2 e2 e2)))
;; ;;  (and (Rf e1 e2 e2) (not (Rf e2 e1 e1)))
;; ;;  (and (Rf e2 e2 e2) (not (Rf e1 e1 e1)))
;; ;; )
;; )))

;; ;;example4
;; (assert (not (=> (and
;;                   (= (join e1 e2) null)
;;                   (Rf e2 null null) (not (= e2 null))
;;                   )
;; (not (Rf e2 e2 e2))
;; )))


;; ;;example5
;; (assert (and
;;          ;; (= (join e1 e2) null)
;;          (= (f (f e1)) e1)
;;          (Rf e1 e2 e2)
;;          (not (= e2 e1))
;;          (not (= e2 (f e1)))
;;          )
;; )




(check-sat)
(exit)

