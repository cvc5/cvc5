(set-option :print-success false)
(set-logic AUFLIAFS)
(set-info :status unsat)
(declare-sort Loc 0)
(define-sort SetLoc () (Set Loc))
(define-sort SetInt () (Set Int))
(declare-sort FldLoc 0)
(declare-sort FldInt 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun lst_1$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun sk_?X_30$0 () SetLoc)
(declare-fun sk_?X_31$0 () SetLoc)
(declare-fun sk_?X_32$0 () SetLoc)
(declare-fun sk_?X_33$0 () SetLoc)
(declare-fun tmp_2$0 () Loc)

(assert (! (forall ((?y Loc))
           (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
               (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y)))
   :named btwn_reach_8))

(assert (! (forall ((?y Loc))
           (or (not (Btwn$0 next$0 tmp_2$0 ?y ?y)) (= tmp_2$0 ?y)
               (Btwn$0 next$0 tmp_2$0 (read$0 next$0 tmp_2$0) ?y)))
   :named btwn_reach_9))

(assert (! (forall ((?y Loc))
           (or (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
               (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) ?y)))
   :named btwn_reach_10))

(assert (! (forall ((?y Loc))
           (or (not (= (read$0 next$0 null$0) null$0))
               (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)))
   :named btwn_cycl_8))

(assert (! (forall ((?y Loc))
           (or (not (= (read$0 next$0 tmp_2$0) tmp_2$0))
               (not (Btwn$0 next$0 tmp_2$0 ?y ?y)) (= tmp_2$0 ?y)))
   :named btwn_cycl_9))

(assert (! (forall ((?y Loc))
           (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
               (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)))
   :named btwn_cycl_10))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0))
   :named btwn_step_8))

(assert (! (Btwn$0 next$0 tmp_2$0 (read$0 next$0 tmp_2$0) (read$0 next$0 tmp_2$0))
   :named btwn_step_9))

(assert (! (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0))
   :named btwn_step_10))

(assert (! (forall ((?f FldLoc))
           (or (set.member (ep$0 ?f sk_?X_30$0 null$0) sk_?X_30$0)
               (= null$0 (ep$0 ?f sk_?X_30$0 null$0))))
   :named entry-point3_10))

(assert (! (forall ((?f FldLoc))
           (or (set.member (ep$0 ?f sk_?X_30$0 lst_1$0) sk_?X_30$0)
               (= lst_1$0 (ep$0 ?f sk_?X_30$0 lst_1$0))))
   :named entry-point3_11))

(assert (! (forall ((?f FldLoc))
           (or (set.member (ep$0 ?f sk_?X_30$0 curr_3$0) sk_?X_30$0)
               (= curr_3$0 (ep$0 ?f sk_?X_30$0 curr_3$0))))
   :named entry-point3_12))

(assert (! (forall ((?f FldLoc))
           (or (set.member (ep$0 ?f sk_?X_30$0 tmp_2$0) sk_?X_30$0)
               (= tmp_2$0 (ep$0 ?f sk_?X_30$0 tmp_2$0))))
   :named entry-point3_13))

(assert (! (forall ((?f FldLoc))
           (Btwn$0 ?f null$0 (ep$0 ?f sk_?X_30$0 null$0)
             (ep$0 ?f sk_?X_30$0 null$0)))
   :named entry-point1_10))

(assert (! (forall ((?f FldLoc))
           (Btwn$0 ?f lst_1$0 (ep$0 ?f sk_?X_30$0 lst_1$0)
             (ep$0 ?f sk_?X_30$0 lst_1$0)))
   :named entry-point1_11))

(assert (! (forall ((?f FldLoc))
           (Btwn$0 ?f curr_3$0 (ep$0 ?f sk_?X_30$0 curr_3$0)
             (ep$0 ?f sk_?X_30$0 curr_3$0)))
   :named entry-point1_12))

(assert (! (forall ((?f FldLoc))
           (Btwn$0 ?f tmp_2$0 (ep$0 ?f sk_?X_30$0 tmp_2$0)
             (ep$0 ?f sk_?X_30$0 tmp_2$0)))
   :named entry-point1_13))

(assert (! (forall ((?f FldLoc) (?y Loc))
           (or (Btwn$0 ?f null$0 (ep$0 ?f sk_?X_30$0 null$0) ?y)
               (not (Btwn$0 ?f null$0 ?y ?y)) (not (set.member ?y sk_?X_30$0))))
   :named entry-point4_10))

(assert (! (forall ((?f FldLoc) (?y Loc))
           (or (Btwn$0 ?f lst_1$0 (ep$0 ?f sk_?X_30$0 lst_1$0) ?y)
               (not (Btwn$0 ?f lst_1$0 ?y ?y)) (not (set.member ?y sk_?X_30$0))))
   :named entry-point4_11))

(assert (! (forall ((?f FldLoc) (?y Loc))
           (or (Btwn$0 ?f curr_3$0 (ep$0 ?f sk_?X_30$0 curr_3$0) ?y)
               (not (Btwn$0 ?f curr_3$0 ?y ?y)) (not (set.member ?y sk_?X_30$0))))
   :named entry-point4_12))

(assert (! (forall ((?f FldLoc) (?y Loc))
           (or (Btwn$0 ?f tmp_2$0 (ep$0 ?f sk_?X_30$0 tmp_2$0) ?y)
               (not (Btwn$0 ?f tmp_2$0 ?y ?y)) (not (set.member ?y sk_?X_30$0))))
   :named entry-point4_13))

(assert (! (forall ((?f FldLoc) (?y Loc))
           (or (not (Btwn$0 ?f null$0 ?y ?y)) (not (set.member ?y sk_?X_30$0))
               (set.member (ep$0 ?f sk_?X_30$0 null$0) sk_?X_30$0)))
   :named entry-point2_10))

(assert (! (forall ((?f FldLoc) (?y Loc))
           (or (not (Btwn$0 ?f lst_1$0 ?y ?y)) (not (set.member ?y sk_?X_30$0))
               (set.member (ep$0 ?f sk_?X_30$0 lst_1$0) sk_?X_30$0)))
   :named entry-point2_11))

(assert (! (forall ((?f FldLoc) (?y Loc))
           (or (not (Btwn$0 ?f curr_3$0 ?y ?y)) (not (set.member ?y sk_?X_30$0))
               (set.member (ep$0 ?f sk_?X_30$0 curr_3$0) sk_?X_30$0)))
   :named entry-point2_12))

(assert (! (forall ((?f FldLoc) (?y Loc))
           (or (not (Btwn$0 ?f tmp_2$0 ?y ?y)) (not (set.member ?y sk_?X_30$0))
               (set.member (ep$0 ?f sk_?X_30$0 tmp_2$0) sk_?X_30$0)))
   :named entry-point2_13))

(assert (! (= (read$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) curr_3$0)
     (read$0 next$0 tmp_2$0))
   :named read_write2))

(assert (! (or (= null$0 curr_3$0)
       (= (read$0 next$0 null$0)
         (read$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) null$0)))
   :named read_write1))

(assert (! (or (= tmp_2$0 curr_3$0)
       (= (read$0 next$0 tmp_2$0)
         (read$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) tmp_2$0)))
   :named read_write1_1))

(assert (! (or (= curr_3$0 curr_3$0)
       (= (read$0 next$0 curr_3$0)
         (read$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) curr_3$0)))
   :named read_write1_2))

(assert (! (= (read$0 next$0 null$0) null$0) :named read_null_5))

(assert (! (= (read$0 next_1$0 null$0) null$0) :named read_null_6))

(assert (! (forall ((l1 Loc))
           (or
               (and (Btwn$0 next$0 lst$0 l1 curr_2$0)
                    (set.member l1 (lseg_domain$0 next$0 lst$0 curr_2$0))
                    (not (= l1 curr_2$0)))
               (and
                    (or (= l1 curr_2$0)
                        (not (Btwn$0 next$0 lst$0 l1 curr_2$0)))
                    (not (set.member l1 (lseg_domain$0 next$0 lst$0 curr_2$0))))))
   :named lseg_footprint_20))

(assert (! (forall ((l1 Loc))
           (or
               (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                    (set.member l1 (lseg_domain$0 next$0 curr_3$0 null$0))
                    (not (= l1 null$0)))
               (and
                    (or (= l1 null$0)
                        (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                    (not (set.member l1 (lseg_domain$0 next$0 curr_3$0 null$0))))))
   :named lseg_footprint_21))

(assert (! (not (set.member tmp_2$0 FP_2$0)) :named check_free_31_6))

(assert (! (not (set.member null$0 Alloc$0)) :named framecondition_of_remove_loop_18_4_15))

(assert (! (not (= lst$0 null$0)) :named if_else_13_6_4))

(assert (! (= FP_Caller$0 (set.union FP$0 FP_Caller$0))
   :named precondition_of_remove_10_11_20))

(assert (! (= sk_?X_33$0 FP$0) :named precondition_of_remove_10_11_21))

(assert (! (lseg_struct$0 sk_?X_32$0 next$0 lst$0 curr_2$0) :named invariant_18_4_62))

(assert (! (= FP$0 (set.union FP_1$0 FP$0)) :named invariant_18_4_63))

(assert (! (= sk_?X_31$0 (lseg_domain$0 next$0 curr_2$0 null$0))
   :named invariant_18_4_64))

(assert (! (= sk_?X_30$0 (set.union sk_?X_31$0 sk_?X_32$0)) :named invariant_18_4_65))

(assert (! (= (as set.empty SetLoc) (as set.empty SetLoc)) :named invariant_18_4_66))

(assert (! (lseg_struct$0 sk_?X_28$0 next$0 curr_3$0 null$0)
   :named invariant_18_4_67))

(assert (! (= sk_?X_29$0 (set.union sk_?X_28$0 sk_?X_27$0)) :named invariant_18_4_68))

(assert (! (= sk_?X_28$0 (lseg_domain$0 next$0 curr_3$0 null$0))
   :named invariant_18_4_69))

(assert (! (= (as set.empty SetLoc) (set.inter sk_?X_27$0 sk_?X_28$0))
   :named invariant_18_4_70))

(assert (! (= Alloc$0 (set.union FP_Caller$0 Alloc$0))
   :named initial_footprint_of_remove_10_11_10))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0)
   :named framecondition_of_remove_loop_18_4_16))

(assert (! (= next_1$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)))
   :named assign_30_6))

(assert (! (= curr_2$0 lst$0) :named assign_17_4_4))

(assert (! (= FP_2$0
     (set.union (set.minus FP$0 FP_1$0)
       (set.union (set.inter Alloc$0 FP_1$0) (set.minus Alloc$0 Alloc$0))))
   :named framecondition_of_remove_loop_18_4_17))

(assert (! (or (Btwn$0 next$0 lst$0 curr_2$0 curr_2$0)
       (not (lseg_struct$0 sk_?X_32$0 next$0 lst$0 curr_2$0)))
   :named unnamed_23))

(assert (! (or (Btwn$0 next$0 curr_3$0 null$0 null$0)
       (not (lseg_struct$0 sk_?X_28$0 next$0 curr_3$0 null$0)))
   :named unnamed_24))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0))
   :named unnamed_25))

(assert (! (forall ((l1 Loc))
           (or
               (and (Btwn$0 next$0 lst_1$0 l1 curr_3$0)
                    (set.member l1 (lseg_domain$0 next$0 lst_1$0 curr_3$0))
                    (not (= l1 curr_3$0)))
               (and
                    (or (= l1 curr_3$0)
                        (not (Btwn$0 next$0 lst_1$0 l1 curr_3$0)))
                    (not (set.member l1 (lseg_domain$0 next$0 lst_1$0 curr_3$0))))))
   :named lseg_footprint_22))

(assert (! (forall ((l1 Loc))
           (or
               (and (Btwn$0 next$0 lst$0 l1 null$0)
                    (set.member l1 (lseg_domain$0 next$0 lst$0 null$0))
                    (not (= l1 null$0)))
               (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                    (not (set.member l1 (lseg_domain$0 next$0 lst$0 null$0))))))
   :named lseg_footprint_23))

(assert (! (forall ((l1 Loc))
           (or
               (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                    (set.member l1 (lseg_domain$0 next$0 curr_2$0 null$0))
                    (not (= l1 null$0)))
               (and
                    (or (= l1 null$0)
                        (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                    (not (set.member l1 (lseg_domain$0 next$0 curr_2$0 null$0))))))
   :named lseg_footprint_24))

(assert (! (not (set.member null$0 Alloc$0)) :named initial_footprint_of_remove_10_11_11))

(assert (! (not (= tmp_2$0 null$0)) :named if_else_28_8_2))

(assert (! (lseg_struct$0 sk_?X_33$0 next$0 lst$0 null$0)
   :named precondition_of_remove_10_11_22))

(assert (! (= sk_?X_33$0 (lseg_domain$0 next$0 lst$0 null$0))
   :named precondition_of_remove_10_11_23))

(assert (! (not (= curr_2$0 null$0)) :named invariant_18_4_71))

(assert (! (lseg_struct$0 sk_?X_31$0 next$0 curr_2$0 null$0)
   :named invariant_18_4_72))

(assert (! (= sk_?X_32$0 (lseg_domain$0 next$0 lst$0 curr_2$0))
   :named invariant_18_4_73))

(assert (! (= sk_?X_30$0 FP_1$0) :named invariant_18_4_74))

(assert (! (= (as set.empty SetLoc) (set.inter sk_?X_32$0 sk_?X_31$0))
   :named invariant_18_4_75))

(assert (! (not (= curr_3$0 null$0)) :named invariant_18_4_76))

(assert (! (lseg_struct$0 sk_?X_27$0 next$0 lst_1$0 curr_3$0)
   :named invariant_18_4_77))

(assert (! (= sk_?X_29$0
     (set.union (set.inter Alloc$0 FP_1$0) (set.minus Alloc$0 Alloc$0)))
   :named invariant_18_4_78))

(assert (! (= sk_?X_27$0 (lseg_domain$0 next$0 lst_1$0 curr_3$0))
   :named invariant_18_4_79))

(assert (! (= (as set.empty SetLoc) (as set.empty SetLoc)) :named invariant_18_4_80))

(assert (! (= Alloc$0 (set.union FP_2$0 Alloc$0))
   :named framecondition_of_remove_loop_18_4_18))

(assert (! (= tmp_2$0 (read$0 next$0 curr_3$0)) :named assign_27_4_2))

(assert (! (= lst_1$0 lst$0) :named framecondition_of_remove_loop_18_4_19))

(assert (! (= FP_Caller_1$0 (set.minus FP_Caller$0 FP$0)) :named assign_13_2_5))

(assert (! (or (Btwn$0 next$0 lst_1$0 curr_3$0 curr_3$0)
       (not (lseg_struct$0 sk_?X_27$0 next$0 lst_1$0 curr_3$0)))
   :named unnamed_26))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
       (not (lseg_struct$0 sk_?X_33$0 next$0 lst$0 null$0)))
   :named unnamed_27))

(assert (! (or (Btwn$0 next$0 curr_2$0 null$0 null$0)
       (not (lseg_struct$0 sk_?X_31$0 next$0 curr_2$0 null$0)))
   :named unnamed_28))

(assert (! (forall ((?u Loc) (?v Loc) (?z Loc))
           (and
                (or
                    (Btwn$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0))
                      ?z ?u ?v)
                    (not
                         (or
                             (and (Btwn$0 next$0 ?z ?u ?v)
                                  (or (Btwn$0 next$0 ?z ?v curr_3$0)
                                      (and (Btwn$0 next$0 ?z ?v ?v)
                                           (not
                                                (Btwn$0 next$0 ?z curr_3$0
                                                  curr_3$0)))))
                             (and (not (= curr_3$0 ?v))
                                  (or (Btwn$0 next$0 ?z curr_3$0 ?v)
                                      (and
                                           (Btwn$0 next$0 ?z curr_3$0
                                             curr_3$0)
                                           (not (Btwn$0 next$0 ?z ?v ?v))))
                                  (Btwn$0 next$0 ?z ?u curr_3$0)
                                  (or
                                      (Btwn$0 next$0 (read$0 next$0 tmp_2$0)
                                        ?v curr_3$0)
                                      (and
                                           (Btwn$0 next$0
                                             (read$0 next$0 tmp_2$0) ?v ?v)
                                           (not
                                                (Btwn$0 next$0
                                                  (read$0 next$0 tmp_2$0)
                                                  curr_3$0 curr_3$0)))))
                             (and (not (= curr_3$0 ?v))
                                  (or (Btwn$0 next$0 ?z curr_3$0 ?v)
                                      (and
                                           (Btwn$0 next$0 ?z curr_3$0
                                             curr_3$0)
                                           (not (Btwn$0 next$0 ?z ?v ?v))))
                                  (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?u
                                    ?v)
                                  (or
                                      (Btwn$0 next$0 (read$0 next$0 tmp_2$0)
                                        ?v curr_3$0)
                                      (and
                                           (Btwn$0 next$0
                                             (read$0 next$0 tmp_2$0) ?v ?v)
                                           (not
                                                (Btwn$0 next$0
                                                  (read$0 next$0 tmp_2$0)
                                                  curr_3$0 curr_3$0))))))))
                (or
                    (and (Btwn$0 next$0 ?z ?u ?v)
                         (or (Btwn$0 next$0 ?z ?v curr_3$0)
                             (and (Btwn$0 next$0 ?z ?v ?v)
                                  (not (Btwn$0 next$0 ?z curr_3$0 curr_3$0)))))
                    (and (not (= curr_3$0 ?v))
                         (or (Btwn$0 next$0 ?z curr_3$0 ?v)
                             (and (Btwn$0 next$0 ?z curr_3$0 curr_3$0)
                                  (not (Btwn$0 next$0 ?z ?v ?v))))
                         (Btwn$0 next$0 ?z ?u curr_3$0)
                         (or
                             (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v
                               curr_3$0)
                             (and
                                  (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v
                                    ?v)
                                  (not
                                       (Btwn$0 next$0 (read$0 next$0 tmp_2$0)
                                         curr_3$0 curr_3$0)))))
                    (and (not (= curr_3$0 ?v))
                         (or (Btwn$0 next$0 ?z curr_3$0 ?v)
                             (and (Btwn$0 next$0 ?z curr_3$0 curr_3$0)
                                  (not (Btwn$0 next$0 ?z ?v ?v))))
                         (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?u ?v)
                         (or
                             (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v
                               curr_3$0)
                             (and
                                  (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v
                                    ?v)
                                  (not
                                       (Btwn$0 next$0 (read$0 next$0 tmp_2$0)
                                         curr_3$0 curr_3$0)))))
                    (not
                         (Btwn$0
                           (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0))
                           ?z ?u ?v)))))
   :named btwn_write))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named btwn_refl_5))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y)))
   :named btwn_sndw_5))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
               (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y)))
   :named btwn_ord1_5))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?z))
               (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z))))
   :named btwn_ord2_5))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
               (Btwn$0 next$0 ?x ?z ?z)))
   :named btwn_trn1_5))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
               (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z))))
   :named btwn_trn2_5))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
               (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z))))
   :named btwn_trn3_5))

(check-sat)
(exit)
