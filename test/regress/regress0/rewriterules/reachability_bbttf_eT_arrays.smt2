;; Back to the Future ... Shuvendu K.Lhiri, Shaz Qadeer
(set-logic AUFLIA)
(set-info :status unsat)

(declare-sort elt 0)
(define-sort mem () (Array elt elt))

(declare-fun R (mem elt elt elt) Bool)

;; reflexive
(assert-propagation ((?m mem)(?x elt)) ((?m ?x)) () () (R ?m ?x ?x ?x) )
;; step
(assert-propagation ((?m mem)(?x elt)) (((select ?m ?x))) () () (R ?m ?x (select ?m ?x) (select ?m ?x)) )
;; (assert-propagation ((?x elt)) (f ?x)))) () () (Rf ?x (f ?x) (f ?x)) (((Rf ?x (f ?x) )
;; (assert-propagation ((?x elt)) (((f ?x))) () () (=> true (Rf ?x (f ?x) (f ?x))) )

;; reach
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)) (((select ?m ?x1))) () ((R ?m ?x1 ?x2 ?x2)) (or (= ?x1 ?x2) (R ?m ?x1 (select ?m ?x1) ?x2)) )
;; ;; reach extended
;; (assert-propagation ((?x1 elt)(?x2 elt)) (((Rf ?x1 (f ?x1) ?x2))) ((not (= ?x1 ?x2))(Rf ?x1 ?x2 ?x2)) () (Rf ?x1 (f ?x1) ?x2) )
;; ;; reach extended
;; (assert-propagation ((?x1 elt)(?x2 elt)) (((Rf ?x1 (f ?x1) ?x2))) ((not (Rf ?x1 (f ?x1) ?x2))(Rf ?x1 ?x2 ?x2)) () (= ?x1 ?x2) )

;; cycle
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)) (((select ?m ?x1))) ((= (select ?m ?x1) ?x1)) ((R ?m ?x1 ?x2 ?x2)) (= ?x1 ?x2) )
;; (assert-propagation ((?x1 elt)(?x2 elt)) () ((= (f ?x1) ?x1)) ((Rf ?x1 ?x2 ?x2)) (= ?x1 ?x2) )

;; (assert-propagation ((?x1 elt)(?x2 elt)) (((Rf ?x1 ?x2 ?x2)(f ?x1))) () () (=> (and (= (f ?x1) ?x1) (Rf ?x1 ?x2 ?x2)) (= ?x1 ?x2)) )

;; sandwich
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)) () () ((R ?m ?x1 ?x2 ?x1)) (= ?x1 ?x2) )
;; (assert-propagation ((?x1 elt)(?x2 elt)) (((Rf ?x1 ?x2 ?x1))) () () (=> (Rf ?x1 ?x2 ?x1) (= ?x1 ?x2)) )

;; order1
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)(?x3 elt)) () ()
                    ((R ?m ?x1 ?x2 ?x2)(R ?m ?x1 ?x3 ?x3)) (or (R ?m ?x1 ?x2 ?x3) (R ?m ?x1 ?x3 ?x2)) )

;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))) () ()
;;                     (=> (and (Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)) (or (Rf ?x1 ?x2 ?x3) (Rf ?x1 ?x3 ?x2))) )

;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x1 ?x2 ?x3))) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
;;                     (Rf ?x1 ?x2 ?x3) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x1 ?x3 ?x2))) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
;;                     (Rf ?x1 ?x3 ?x2) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x1 ?x3 ?x2))) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
;;                     (Rf ?x1 ?x2 ?x3) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x1 ?x2 ?x3))) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
;;                     (Rf ?x1 ?x3 ?x2) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
;;                     (Rf ?x1 ?x2 ?x3) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
;;                     (Rf ?x1 ?x3 ?x2) )

;; order2
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)(?x3 elt)) () () ((R ?m ?x1 ?x2 ?x3))
                    (and (R ?m ?x1 ?x2 ?x2) (R ?m ?x2 ?x3 ?x3)) )
;; transitive1
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)(?x3 elt)) () () ((R ?m ?x1 ?x2 ?x2)(R ?m ?x2 ?x3 ?x3))
                    (R ?m ?x1 ?x3 ?x3) )
;; ;; transitive1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () () ((not (Rf ?x1 ?x3 ?x3))(Rf ?x2 ?x3 ?x3))
;;                     (not (Rf ?x1 ?x2 ?x2)) )
;; ;; transitive1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () () ((Rf ?x1 ?x2 ?x2)(not (Rf ?x1 ?x3 ?x3)))
;;                     (not (Rf ?x2 ?x3 ?x3)) )

;;transitive2
(assert-propagation ((?m mem)(?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () () ((R ?m ?x0 ?x1 ?x2)(R ?m ?x1 ?x3 ?x2))
                    (and (R ?m ?x0 ?x1 ?x3) (R ?m ?x0 ?x3 ?x2)) )

;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x0 ?x1 ?x2)(Rf ?x1 ?x3 ?x2))) () ()
;;                     (=> (and (Rf ?x0 ?x1 ?x2)(Rf ?x1 ?x3 ?x2))
;;                         (and (Rf ?x0 ?x1 ?x3) (Rf ?x0 ?x3 ?x2)))
;;                     )

;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x0 ?x1 ?x2))) () ((not (Rf ?x0 ?x1 ?x3))(Rf ?x1 ?x3 ?x2))
;;                     (not (Rf ?x0 ?x1 ?x2)) )
;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x1 ?x3 ?x2))) () ((Rf ?x0 ?x1 ?x2)(not (Rf ?x0 ?x1 ?x3)))
;;                     (not (Rf ?x1 ?x3 ?x2)) )
;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x0 ?x1 ?x2))) () ((not (Rf ?x0 ?x3 ?x2))(Rf ?x1 ?x3 ?x2))
;;                     (not (Rf ?x0 ?x1 ?x2)) )
;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x1 ?x3 ?x2))) () ((Rf ?x0 ?x1 ?x2)(not (Rf ?x0 ?x3 ?x2)))
;;                     (not (Rf ?x1 ?x3 ?x2)) )

;; ;;transitive3
(assert-propagation ((?m mem)(?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () () ((R ?m ?x0 ?x1 ?x2)(R ?m ?x0 ?x3 ?x1))
                    (and (R ?m ?x0 ?x3 ?x2) (R ?m ?x3 ?x1 ?x2)) )

;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) (((Rf ?x0 ?x1 ?x2)(Rf ?x0 ?x3 ?x1))) () ()
;;                     (=> (and (Rf ?x0 ?x1 ?x2)(Rf ?x0 ?x3 ?x1))
;;                         (and (Rf ?x0 ?x3 ?x2) (Rf ?x3 ?x1 ?x2))) )


(declare-fun next () mem)

(declare-fun e1 () elt)
(declare-fun e2 () elt)
(declare-fun e3 () elt)
(declare-fun e4 () elt)



(declare-fun R_avoid (mem elt elt elt) Bool)

(assert-rewrite ((?m mem)(?x0 elt)(?x1 elt)(?exc elt)) () () (R_avoid ?m ?x0 ?x1 ?exc)
                 (or (R ?m ?x0 ?x1 ?exc) (and (R ?m ?x0 ?x1 ?x1) (not (R ?m ?x0 ?exc ?exc)))) )


;; Identity of Back to the future p175
(assert-rewrite ((?p elt)(?q elt)(?u elt)(?v elt)(?w elt)(?m mem)) () () (R (store ?m ?p ?q) ?u ?v ?w)
                (or (and (R ?m ?u ?v ?w) (R_avoid ?m ?u ?w ?p) )
                    (and (not (= ?p ?w)) (R_avoid ?m ?u ?p ?w) (R ?m ?u ?v ?p) (R_avoid ?m ?q ?w ?p) )
                    (and (not (= ?p ?w)) (R_avoid ?m ?u ?p ?w) (R ?m ?q ?v ?w) (R_avoid ?m ?q ?w ?p) ) )
                )



(declare-fun join (mem elt elt) elt)

(declare-fun null () elt)
(assert (= (select next null) null))

(assert-propagation ((?m mem)(?x elt)(?y elt)(?z elt)) (((join ?m ?x ?y))) () ((R ?m ?x ?z ?z)(R ?m ?y ?z ?z)) (R ?m ?x (join ?m ?x ?y) ?z) )
(assert-propagation ((?m mem)(?x elt)(?y elt)) (((join ?m ?x ?y))) () () (or (and (R ?m ?x (join ?m ?x ?y) (join ?m ?x ?y)) (R ?m ?y (join ?m ?x ?y) (join ?m ?x ?y))) (= (join ?m ?x ?y) null))  )

;;extended join
(assert-propagation ((?m mem)(?x elt)(?y elt)(?z elt)) () () ((R ?m ?x ?z (join ?m ?x ?y))(R ?m ?y ?z (join ?m ?x ?y))) (= ?z (join ?m ?x ?y)) )


(assert-propagation ((?p elt)(?q elt)(?m mem)(?u elt)(?v elt)) (((join (store ?m ?p ?q) ?u ?v))) () ()
                    (= (join (store ?m ?p ?q) ?u ?v)
                       (let ((jp (join ?m ?u ?v)))
                         ;; In ?m: ?u ?v have a nearest point of junction (join ?m ?u ?v)
                         (ite (and (R ?m ?u jp jp) (R ?m ?v jp jp))
                              ;; The modification is in the ?u branch
                              (ite (R ?m ?u ?p jp)
                                   ;; we can go by the new path and the new path doesn't cycle
                                   (ite (and (R (store ?m ?p ?q) ?u ?p ?q) (R (store ?m ?p ?q) ?q (join ?m ?q ?v) (join ?m ?q ?v)))
                                        (join ?m ?q ?v)
                                   ;; we can't
                                        null
                                   )
                              ;; The modification is in the ?v branch
                              (ite (R ?m ?v ?p jp)
                                   ;; we can go by the new path and the new path doesn't cycle
                                   (ite (and (R (store ?m ?p ?q) ?v ?p ?q) (R (store ?m ?p ?q) ?q (join ?m ?u ?q) (join ?m ?u ?q)))
                                        (join ?m ?u ?q)
                                   ;; we can't
                                        null
                                   )
                              ;; The modification is not before the point of junction
                                   (join ?m ?u ?v)
                              ))
                         ;; In ?m: ?u ?v doens't have a point of junction
                              ;;The modification is accesible from ?u
                              (ite (R ?m ?u ?p ?p) (join ?m ?q ?v)
                              ;;The modification is accesible from ?v
                                   (ite (R ?m ?v ?p ?p) (join ?m ?u ?q)
                              ;;The modification is accesible neither from ?u neither from ?v
                                        (join ?m ?u ?v)
                                   )
                              )
                         )
                       ))
                                        )

(declare-fun next2 () mem)

;; === Example 0 ===
;; (assert (not (=>
;;               (and (not (= e1 e2))
;;                    (R next e1 e2 e3))
;;               (R next e1 (select next e1) e3))
;; ))

;;================
;;Thomas' example1 x,e1 y,e2 z,e3 y',e4
;;================
;; (assert (not (=>
;;               (and (R next e1 e2 e3)
;;                    (not (= e2 e3))
;;                    (= e4 (select next e2)))
;;               (R next e1 e4 e3))
;; ))


;;===================
;; ;;Thomas' example2
;;===================

;; (assert (not (=>
;;               (and (R next e1 null null)
;;                    (= (join next e1 e2) null)
;;                    (= next2 (store next e2 e1))
;;                    )
;;               (R next2 e1 null null)
;;               )
;;              )
;;         )


;;================
;;Thomas' example3
;;================
(assert (not (=> (and (= (join next e1 e2) null)
                      (R next e2 null null)
                      (not (= e2 null))
                      (= next2 (store next e2 e1))
                      (= e3 e2)
                      (= e4 (select next e2))
                      )
                 (= (join next2 e3 e4) null)
                 )
             )
        )

;; ==== for debugging example 3 ====
;; ;;case to consider
;; ;;(assert (or (not (R next e1 null null)) (R next e1 null null)))

;; ;;first case to consider
;; ;;(assert (R next e1 null null))

;; ;;second case to consider
;; ;; (assert (not (R next e1 null null)))


;; ;;hyp
;; (assert (= (join next e1 e2) null))
;; (assert (R next e2 null null))
;; (assert (not (= e2 null)))
;; (assert (= next2 (store next e2 e1)))
;; (assert (= e3 e2))
;; (assert (= e4 (select next e2)))

;; ;; help
;; ;; have a join point
;; ;; (assert (R next e2 e4 e4))
;; ;; (assert (R next e4 e4 e4))

;; ;; (assert (R next e2 (join next e2 e4) e4))
;; ;; (assert (not (R next e4 e2 e2)))

;; ;; (assert (not (= e2 (join next e2 e4))));;  slow with efficient (/axioms)

;; ;; (assert (= e4 (join next e2 e4))) ;; unprovable with efficient (/axioms)
;; ;; in e2 branch
;; ;; (assert (not (R next e4 e2 null))) ;; 
;; ;; the auxillary join
;; ;; (assert (= (join next2 e1 e4) null))


;; ;;to prove
;; (assert (not (= (join next2 e3 e4) null)))


;;====================
;; ;;Thomas' example wrong sat?
;;====================

;; (assert (not (=> (and
;;                   (= (join next e1 e2) null)
;;                   (R next e2 null null)
;;                   (not (= e2 null))
;;                   (= next2 (store next e2 e1))
;;                   )
;;                  (= (join next2 e1 e2) null)
;;                  )
;;              )
;;         )

;;====================
;; ;;example4 sat
;;====================

;; (assert (not (=> (and
;;                   (= (join next e1 e2) null)
;;                   (R next e2 null null) (not (= e2 null))
;;                   )
;; (not (R next e2 e2 e2))
;; )))


;;====================
;;example5 unsat
;;====================

;; (assert (and
;;          ;; (= (join e1 e2) null)
;;          (= (select next (select next e1)) e1)
;;          (R next e1 e2 e2)
;;          (not (= e2 e1))
;;          (not (= e2 (select next e1)))
;;          )
;; )

;;====================
;; ;; example 6 unsat
;;====================

;; ;; join is the nearest junction point
;; (assert (and (not (= e3 (join next e1 e2)))
;;              (R next e1 e3 (join next e1 e2))
;;              (R next e2 e3 (join next e1 e2))
;; ))


;;====================
;; example7 unsat
;;====================

;; (assert (R next e1 e2 (select next e1)))
;; (assert (not (= e1 e2)))
;; (assert (not (= e2 (select next e1))))



(check-sat)
(exit)

