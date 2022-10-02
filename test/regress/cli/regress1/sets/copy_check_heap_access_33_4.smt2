; COMMAND-LINE: --full-saturate-quant
; EXPECT: unsat
(set-option :print-success false)
(set-logic AUFLIAFS)
(set-info :status unsat)
(declare-sort Loc 0)
(define-sort SetLoc () (Set Loc))
(define-sort SetInt () (Set Int))
(declare-sort FldLoc 0)
(declare-sort FldInt 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldInt Loc) Int)
(declare-fun read$1 (FldLoc Loc) Loc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_1$0 () SetLoc)
(declare-fun Axiom_1$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun cp_2$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun data$0 () FldInt)
(declare-fun lst$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun res_1$0 () Loc)
(declare-fun sk_?X_4$0 () SetLoc)
(declare-fun slseg_domain$0 (FldInt FldLoc Loc Loc) SetLoc)
(declare-fun slseg_struct$0 (SetLoc FldInt FldLoc Loc Loc) Bool)
(declare-fun tmp_2$0 () Loc)

(assert (! (forall ((?y Loc))
           (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
               (Btwn$0 next$0 null$0 (read$1 next$0 null$0) ?y)))
   :named btwn_reach_1))

(assert (! (forall ((?y Loc))
           (or (not (= (read$1 next$0 null$0) null$0))
               (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)))
   :named btwn_cycl_1))

(assert (! (Btwn$0 next$0 null$0 (read$1 next$0 null$0) (read$1 next$0 null$0))
   :named btwn_step_1))

(assert (! (forall ((l1 Loc) (l2 Loc))
           (or (not Axiom_1$0)
               (or (<= (read$0 data$0 l1) (read$0 data$0 l2))
                   (not (Btwn$0 next$0 l1 l2 null$0)) (not (set.member l1 sk_?X_4$0))
                   (not (set.member l2 sk_?X_4$0)))))
   :named sortedness_3))

(assert (! (= (read$1 next$0 null$0) null$0) :named read_null_1))

(assert (! (not (set.member tmp_2$0 Alloc$0)) :named new_31_11))

(assert (! (not (set.member null$0 Alloc$0)) :named initial_footprint_of_copy_23_11_2))

(assert (! (not (= lst$0 null$0)) :named if_else_26_6))

(assert (! (= FP_Caller$0 (set.union FP$0 FP_Caller$0))
   :named precondition_of_copy_23_11_4))

(assert (! (= sk_?X_4$0 FP$0) :named precondition_of_copy_23_11_5))

(assert (! (= res_1$0 tmp_2$0) :named assign_31_4))

(assert (! (= cp_2$0 res_1$0) :named assign_32_4))

(assert (! (= FP_1$0 (set.union FP$0 (set.singleton tmp_2$0))) :named assign_31_11))

(assert (! (or (and (Btwn$0 next$0 lst$0 null$0 null$0) Axiom_1$0)
       (not (slseg_struct$0 sk_?X_4$0 data$0 next$0 lst$0 null$0)))
   :named unnamed_3))

(assert (! (forall ((l1 Loc))
           (or
               (and (Btwn$0 next$0 lst$0 l1 null$0)
                    (set.member l1 (slseg_domain$0 data$0 next$0 lst$0 null$0))
                    (not (= l1 null$0)))
               (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                    (not (set.member l1 (slseg_domain$0 data$0 next$0 lst$0 null$0))))))
   :named slseg_footprint_2))

(assert (! (not (set.member curr_2$0 FP_1$0)) :named check_heap_access_33_4))

(assert (! (not (= tmp_2$0 null$0)) :named new_31_11_1))

(assert (! (slseg_struct$0 sk_?X_4$0 data$0 next$0 lst$0 null$0)
   :named precondition_of_copy_23_11_6))

(assert (! (= sk_?X_4$0 (slseg_domain$0 data$0 next$0 lst$0 null$0))
   :named precondition_of_copy_23_11_7))

(assert (! (= Alloc$0 (set.union FP_Caller$0 Alloc$0))
   :named initial_footprint_of_copy_23_11_3))

(assert (! (= curr_2$0 lst$0) :named assign_30_4))

(assert (! (= FP_Caller_1$0 (set.minus FP_Caller$0 FP$0)) :named assign_26_2_1))

(assert (! (= Alloc_1$0 (set.union Alloc$0 (set.singleton tmp_2$0))) :named assign_31_11_1))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named btwn_refl_1))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y)))
   :named btwn_sndw_1))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
               (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y)))
   :named btwn_ord1_1))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?z))
               (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z))))
   :named btwn_ord2_1))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
               (Btwn$0 next$0 ?x ?z ?z)))
   :named btwn_trn1_1))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
               (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z))))
   :named btwn_trn2_1))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
               (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z))))
   :named btwn_trn3_1))

(check-sat)
(exit)
