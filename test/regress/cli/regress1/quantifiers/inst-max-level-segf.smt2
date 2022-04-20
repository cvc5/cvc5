; DISABLE-TESTER: lfsc
; COMMAND-LINE: --inst-max-level=0 --simplification=none
; EXPECT: unsat
(set-logic UF)
(set-info :status unsat)
(declare-sort Node 0)
(declare-sort GrassPat 0)
(declare-sort GrassArray 1)
(declare-sort ArrayCell 1)
(declare-sort Loc 1)
(declare-sort Set 1)
(declare-sort Map 2)
(declare-sort GrassByte 0)
(declare-fun grass_null$0 () (Loc Node))
(declare-fun grass_read$0 ((Map (Loc Node) (Loc Node)) (Loc Node))
             (Loc Node))
(declare-fun grass_set.empty$0 () (Set (Loc Node)))
(declare-fun grass_singleton$0 ((Loc Node)) (Set (Loc Node)))
(declare-fun grass_union$0 ((Set (Loc Node)) (Set (Loc Node)))
             (Set (Loc Node)))
(declare-fun grass_intersection$0 ((Set (Loc Node)) (Set (Loc Node)))
             (Set (Loc Node)))
(declare-fun grass_setminus$0 ((Set (Loc Node)) (Set (Loc Node)))
             (Set (Loc Node)))
(declare-fun grass_Btwn$0 ((Map (Loc Node) (Loc Node)) (Loc Node) (Loc Node)
             (Loc Node)) Bool)
(declare-fun grass_member$0 ((Loc Node) (Set (Loc Node))) Bool)
(declare-fun grass_known$0 ((Map (Loc Node) (Loc Node))) GrassPat)
(declare-fun grass_known$1 (Bool) GrassPat)
(declare-fun Alloc_Node$0 () (Set (Loc Node)))
(declare-fun FP_Caller_Node$0 () (Set (Loc Node)))
(declare-fun FP_Caller_Node_1$0 () (Set (Loc Node)))
(declare-fun FP_Caller_final_Node_2$0 () (Set (Loc Node)))
(declare-fun FP_Node$0 () (Set (Loc Node)))
(declare-fun Label$0 () Bool)
(declare-fun Label_1$0 () Bool)
(declare-fun Label_2$0 () Bool)
(declare-fun Label_3$0 () Bool)
(declare-fun elt$0 () (Loc Node))
(declare-fun lseg$0 ((Map (Loc Node) (Loc Node)) (Loc Node) (Loc Node)
             (Set (Loc Node))) Bool)
(declare-fun lst$0 () (Loc Node))
(declare-fun next$0 () (Map (Loc Node) (Loc Node)))
(declare-fun res_2$0 () (Loc Node))
(declare-fun set_compr$0 ((Map (Loc Node) (Loc Node)) (Loc Node) (Loc Node))
             (Set (Loc Node)))
(declare-fun sk_?X$0 () (Set (Loc Node)))
(declare-fun sk_?X_1$0 () (Set (Loc Node)))
(declare-fun sk_?X_2$0 () (Set (Loc Node)))
(declare-fun sk_?X_3$0 () (Set (Loc Node)))
(declare-fun sk_?X_4$0 () (Set (Loc Node)))
(declare-fun sk_?e$0 () (Loc Node))

(assert (not (grass_member$0 grass_null$0 Alloc_Node$0)))
(assert
        (and
          (or
            (or
              (and (and (grass_member$0 sk_?e$0 sk_?X_4$0) Label_1$0)
                (and
                  (not
                    (grass_member$0 sk_?e$0
                      (set_compr$0 next$0 res_2$0 grass_null$0)))
                  Label_1$0))
              (and
                (and
                  (grass_member$0 sk_?e$0
                    (set_compr$0 next$0 res_2$0 grass_null$0))
                  Label_1$0)
                (and (not (grass_member$0 sk_?e$0 sk_?X_4$0)) Label_1$0)))
            (and
              (not (grass_Btwn$0 next$0 res_2$0 grass_null$0 grass_null$0))
              Label$0))
          Label_2$0))
(assert (forall ((x (Loc Node))) (not (grass_member$0 x grass_set.empty$0))))
(assert
        (forall ((y (Loc Node)) (x (Loc Node)))
                (or (and (= x y) (grass_member$0 x (grass_singleton$0 y)))
                  (and (not (= x y))
                    (not (grass_member$0 x (grass_singleton$0 y)))))))
(assert
        (forall ((x (Loc Node)))
                (or
                  (and (grass_member$0 x FP_Caller_Node$0)
                    (grass_member$0 x
                      (grass_setminus$0 FP_Caller_Node$0 FP_Node$0))
                    (not (grass_member$0 x FP_Node$0)))
                  (and
                    (or (grass_member$0 x FP_Node$0)
                      (not (grass_member$0 x FP_Caller_Node$0)))
                    (not
                      (grass_member$0 x
                        (grass_setminus$0 FP_Caller_Node$0 FP_Node$0)))))))
(assert
        (forall ((x (Loc Node)))
                (or
                  (and (grass_member$0 x Alloc_Node$0)
                    (grass_member$0 x
                      (grass_setminus$0 Alloc_Node$0 Alloc_Node$0))
                    (not (grass_member$0 x Alloc_Node$0)))
                  (and
                    (or (grass_member$0 x Alloc_Node$0)
                      (not (grass_member$0 x Alloc_Node$0)))
                    (not
                      (grass_member$0 x
                        (grass_setminus$0 Alloc_Node$0 Alloc_Node$0)))))))
(assert
        (forall ((x (Loc Node)))
                (or
                  (and (grass_member$0 x Alloc_Node$0)
                    (grass_member$0 x FP_Node$0)
                    (grass_member$0 x
                      (grass_intersection$0 Alloc_Node$0 FP_Node$0)))
                  (and
                    (or (not (grass_member$0 x Alloc_Node$0))
                      (not (grass_member$0 x FP_Node$0)))
                    (not
                      (grass_member$0 x
                        (grass_intersection$0 Alloc_Node$0 FP_Node$0)))))))
(assert
        (forall ((x (Loc Node)))
                (or
                  (and (grass_member$0 x sk_?X$0)
                    (grass_member$0 x sk_?X_1$0)
                    (grass_member$0 x
                      (grass_intersection$0 sk_?X$0 sk_?X_1$0)))
                  (and
                    (or (not (grass_member$0 x sk_?X$0))
                      (not (grass_member$0 x sk_?X_1$0)))
                    (not
                      (grass_member$0 x
                        (grass_intersection$0 sk_?X$0 sk_?X_1$0)))))))
(assert
        (forall ((x (Loc Node)))
                (or
                  (and
                    (grass_member$0 x
                      (grass_union$0
                        (grass_intersection$0 Alloc_Node$0 FP_Node$0)
                        (grass_setminus$0 Alloc_Node$0 Alloc_Node$0)))
                    (or
                      (grass_member$0 x
                        (grass_intersection$0 Alloc_Node$0 FP_Node$0))
                      (grass_member$0 x
                        (grass_setminus$0 Alloc_Node$0 Alloc_Node$0))))
                  (and
                    (not
                      (grass_member$0 x
                        (grass_intersection$0 Alloc_Node$0 FP_Node$0)))
                    (not
                      (grass_member$0 x
                        (grass_setminus$0 Alloc_Node$0 Alloc_Node$0)))
                    (not
                      (grass_member$0 x
                        (grass_union$0
                          (grass_intersection$0 Alloc_Node$0 FP_Node$0)
                          (grass_setminus$0 Alloc_Node$0 Alloc_Node$0))))))))
(assert
        (forall ((x (Loc Node)))
                (or
                  (and (grass_member$0 x (grass_union$0 sk_?X$0 sk_?X_1$0))
                    (or (grass_member$0 x sk_?X$0)
                      (grass_member$0 x sk_?X_1$0)))
                  (and (not (grass_member$0 x sk_?X$0))
                    (not (grass_member$0 x sk_?X_1$0))
                    (not
                      (grass_member$0 x (grass_union$0 sk_?X$0 sk_?X_1$0)))))))
(assert
        (forall ((x (Loc Node)))
                (or
                  (and
                    (grass_member$0 x
                      (grass_union$0 FP_Caller_Node_1$0 FP_Node$0))
                    (or (grass_member$0 x FP_Caller_Node_1$0)
                      (grass_member$0 x FP_Node$0)))
                  (and (not (grass_member$0 x FP_Caller_Node_1$0))
                    (not (grass_member$0 x FP_Node$0))
                    (not
                      (grass_member$0 x
                        (grass_union$0 FP_Caller_Node_1$0 FP_Node$0)))))))
(assert
        (forall ((x (Loc Node)))
                (or
                  (and
                    (grass_member$0 x
                      (grass_union$0 FP_Node$0 FP_Caller_Node$0))
                    (or (grass_member$0 x FP_Node$0)
                      (grass_member$0 x FP_Caller_Node$0)))
                  (and (not (grass_member$0 x FP_Node$0))
                    (not (grass_member$0 x FP_Caller_Node$0))
                    (not
                      (grass_member$0 x
                        (grass_union$0 FP_Node$0 FP_Caller_Node$0)))))))
(assert
        (forall ((x (Loc Node)))
                (or
                  (and
                    (grass_member$0 x
                      (grass_union$0 FP_Caller_Node$0 Alloc_Node$0))
                    (or (grass_member$0 x FP_Caller_Node$0)
                      (grass_member$0 x Alloc_Node$0)))
                  (and (not (grass_member$0 x FP_Caller_Node$0))
                    (not (grass_member$0 x Alloc_Node$0))
                    (not
                      (grass_member$0 x
                        (grass_union$0 FP_Caller_Node$0 Alloc_Node$0)))))))
(assert
        (or (grass_Btwn$0 next$0 lst$0 lst$0 lst$0)
          (not (lseg$0 next$0 lst$0 lst$0 sk_?X$0))))
(assert
        (forall
                ((next (Map (Loc Node) (Loc Node))) (x (Loc Node))
                 (y (Loc Node)) (z (Loc Node)))
                (or
                  (and (grass_Btwn$0 next x z y)
                    (grass_member$0 z (set_compr$0 next x y)) (not (= z y)))
                  (and (or (= z y) (not (grass_Btwn$0 next x z y)))
                    (not (grass_member$0 z (set_compr$0 next x y)))))))
(assert
        (forall
                ((?u (Loc Node)) (?x (Loc Node)) (?y (Loc Node))
                 (?z (Loc Node)))
                (or (not (grass_Btwn$0 next$0 ?x ?y ?z))
                  (not (grass_Btwn$0 next$0 ?x ?u ?y))
                  (and (grass_Btwn$0 next$0 ?x ?u ?z)
                    (grass_Btwn$0 next$0 ?u ?y ?z)))))
(assert
        (forall
                ((?u (Loc Node)) (?x (Loc Node)) (?y (Loc Node))
                 (?z (Loc Node)))
                (or (not (grass_Btwn$0 next$0 ?x ?y ?z))
                  (not (grass_Btwn$0 next$0 ?y ?u ?z))
                  (and (grass_Btwn$0 next$0 ?x ?y ?u)
                    (grass_Btwn$0 next$0 ?x ?u ?z)))))
(assert
        (forall ((?x (Loc Node)) (?y (Loc Node)) (?z (Loc Node)))
                (or (not (grass_Btwn$0 next$0 ?x ?y ?y))
                  (not (grass_Btwn$0 next$0 ?y ?z ?z))
                  (grass_Btwn$0 next$0 ?x ?z ?z))))
(assert
        (forall ((?x (Loc Node)) (?y (Loc Node)) (?z (Loc Node)))
                (or (not (grass_Btwn$0 next$0 ?x ?y ?z))
                  (and (grass_Btwn$0 next$0 ?x ?y ?y)
                    (grass_Btwn$0 next$0 ?y ?z ?z)))))
(assert
        (forall ((?x (Loc Node)) (?y (Loc Node)) (?z (Loc Node)))
                (or (not (grass_Btwn$0 next$0 ?x ?y ?y))
                  (not (grass_Btwn$0 next$0 ?x ?z ?z))
                  (grass_Btwn$0 next$0 ?x ?y ?z)
                  (grass_Btwn$0 next$0 ?x ?z ?y))))
(assert
        (forall ((?x (Loc Node)) (?y (Loc Node)))
                (or (not (grass_Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))
(assert
        (forall ((?y (Loc Node)))
                (or (not (grass_Btwn$0 next$0 res_2$0 ?y ?y)) (= res_2$0 ?y)
                  (grass_Btwn$0 next$0 res_2$0 (grass_read$0 next$0 res_2$0)
                    ?y))))
(assert
        (forall ((?y (Loc Node)))
                (or (not (grass_Btwn$0 next$0 lst$0 ?y ?y)) (= lst$0 ?y)
                  (grass_Btwn$0 next$0 lst$0 (grass_read$0 next$0 lst$0) ?y))))
(assert
        (forall ((?y (Loc Node)))
                (or (not (= (grass_read$0 next$0 res_2$0) res_2$0))
                  (not (grass_Btwn$0 next$0 res_2$0 ?y ?y)) (= res_2$0 ?y))))
(assert
        (forall ((?y (Loc Node)))
                (or (not (= (grass_read$0 next$0 lst$0) lst$0))
                  (not (grass_Btwn$0 next$0 lst$0 ?y ?y)) (= lst$0 ?y))))
(assert
        (grass_Btwn$0 next$0 res_2$0 (grass_read$0 next$0 res_2$0)
          (grass_read$0 next$0 res_2$0)))
(assert
        (grass_Btwn$0 next$0 lst$0 (grass_read$0 next$0 lst$0)
          (grass_read$0 next$0 lst$0)))
(assert (forall ((?x (Loc Node))) (grass_Btwn$0 next$0 ?x ?x ?x)))
(assert
        (or (= sk_?X$0 (set_compr$0 next$0 lst$0 lst$0))
          (not (lseg$0 next$0 lst$0 lst$0 sk_?X$0))))
(assert (= (grass_read$0 next$0 grass_null$0) grass_null$0))
(assert (= FP_Caller_Node_1$0 (grass_setminus$0 FP_Caller_Node$0 FP_Node$0)))
(assert (and (= lst$0 grass_null$0) Label_3$0))
(assert (= Alloc_Node$0 (grass_union$0 FP_Caller_Node$0 Alloc_Node$0)))
(assert
        (= sk_?X_4$0
          (grass_union$0 (grass_intersection$0 Alloc_Node$0 FP_Node$0)
            (grass_setminus$0 Alloc_Node$0 Alloc_Node$0))))
(assert (= sk_?X_3$0 (grass_union$0 sk_?X$0 sk_?X_2$0)))
(assert (= sk_?X_2$0 sk_?X_1$0))
(assert (= sk_?X_1$0 (grass_singleton$0 elt$0)))
(assert (= (grass_read$0 next$0 elt$0) grass_null$0))
(assert (= FP_Node$0 sk_?X_3$0))
(assert (= FP_Caller_Node$0 (grass_union$0 FP_Node$0 FP_Caller_Node$0)))
(assert (= grass_set.empty$0 (grass_intersection$0 sk_?X$0 sk_?X_2$0)))
(assert (= grass_set.empty$0 grass_set.empty$0))
(assert (lseg$0 next$0 lst$0 grass_null$0 sk_?X$0))
(assert
        (= FP_Caller_final_Node_2$0
          (grass_union$0 FP_Caller_Node_1$0 FP_Node$0)))
(assert (= res_2$0 elt$0))
(assert (= (grass_union$0 FP_Caller_Node$0 Alloc_Node$0) Alloc_Node$0))
(assert (= (grass_read$0 next$0 grass_null$0) grass_null$0))
(assert (= (grass_read$0 next$0 grass_null$0) lst$0))
(assert (= (grass_read$0 next$0 grass_null$0) (grass_read$0 next$0 elt$0)))
(assert
        (= (grass_known$1 (lseg$0 next$0 lst$0 grass_null$0 sk_?X$0))
          (grass_known$1 (lseg$0 next$0 lst$0 lst$0 sk_?X$0))))
(assert (= (grass_intersection$0 sk_?X$0 sk_?X_2$0) grass_set.empty$0))
(assert
        (=
          (grass_union$0 (grass_intersection$0 Alloc_Node$0 FP_Node$0)
            (grass_setminus$0 Alloc_Node$0 Alloc_Node$0))
          sk_?X_4$0))
(assert (= res_2$0 elt$0))
(assert (= (grass_union$0 FP_Node$0 FP_Caller_Node$0) FP_Caller_Node$0))
(assert (= sk_?X_1$0 (grass_singleton$0 elt$0)))
(assert (= sk_?X_1$0 sk_?X_2$0))
(assert
        (= FP_Caller_final_Node_2$0
          (grass_union$0 FP_Caller_Node_1$0 FP_Node$0)))
(assert (= FP_Node$0 sk_?X_3$0))
(assert (= FP_Node$0 (grass_union$0 sk_?X$0 sk_?X_2$0)))
(assert (= FP_Caller_Node_1$0 (grass_setminus$0 FP_Caller_Node$0 FP_Node$0)))
(assert (= sk_?X$0 (set_compr$0 next$0 lst$0 lst$0)))
(assert (= sk_?X$0 (set_compr$0 next$0 lst$0 grass_null$0)))
(check-sat)
