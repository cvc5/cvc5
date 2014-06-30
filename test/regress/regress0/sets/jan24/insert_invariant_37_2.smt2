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
(declare-fun Axiom$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun c1_2$0 () SetInt)
(declare-fun c2_2$0 () SetInt)
(declare-fun content$0 () SetInt)
(declare-fun curr_2$0 () Loc)
(declare-fun data$0 () FldInt)
(declare-fun lst$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun prev_2$0 () Loc)
(declare-fun sk_?X$0 () SetLoc)
(declare-fun sk_?X_1$0 () SetLoc)
(declare-fun sk_?X_2$0 () SetLoc)
(declare-fun sk_?X_3$0 () SetLoc)
(declare-fun sk_?X_4$0 () SetLoc)
(declare-fun sk_?X_5$0 () SetLoc)
(declare-fun sk_?e$0 () Int)
(declare-fun sk_?e_1$0 () Loc)
(declare-fun sk_?e_2$0 () Loc)
(declare-fun sk_?e_3$0 () Int)
(declare-fun sk_FP$0 () SetLoc)
(declare-fun sk_FP_1$0 () SetLoc)
(declare-fun sk_l1$0 () Loc)
(declare-fun sk_l1_1$0 () Loc)
(declare-fun sk_l2$0 () Loc)
(declare-fun sk_l2_1$0 () Loc)
(declare-fun sorted_set_c$0 (FldInt FldLoc Loc Loc) SetInt)
(declare-fun sorted_set_domain$0 (FldInt FldLoc Loc Loc) SetLoc)
(declare-fun sorted_set_struct$0 (SetLoc FldInt FldLoc Loc Loc SetInt) Bool)
(declare-fun val$0 () Int)
(declare-fun witness$0 (Int SetInt) Loc)

(assert (! (forall ((?y Loc))
           (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
               (Btwn$0 next$0 null$0 (read$1 next$0 null$0) ?y)))
   :named btwn_reach))

(assert (! (forall ((?y Loc))
           (or (not (= (read$1 next$0 null$0) null$0))
               (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)))
   :named btwn_cycl))

(assert (! (Btwn$0 next$0 null$0 (read$1 next$0 null$0) (read$1 next$0 null$0))
   :named btwn_step))

(assert (! (forall ((l1 Loc) (l2 Loc))
           (or (not Axiom$0)
               (or (= l1 l2) (< (read$0 data$0 l1) (read$0 data$0 l2))
                   (not (Btwn$0 next$0 l1 l2 null$0)) (not (member l1 sk_?X$0))
                   (not (member l2 sk_?X$0)))))
   :named strict_sortedness))

(assert (! (forall ((l1 Loc))
           (or (= l1 null$0)
               (member (read$0 data$0 l1)
                 (sorted_set_c$0 data$0 next$0 lst$0 null$0))
               (not (Btwn$0 next$0 lst$0 l1 null$0))))
   :named sorted_set_1))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 curr_2$0)
                (sorted_set_c$0 data$0 next$0 lst$0 null$0))
              null$0)
            (member (read$0 data$0 curr_2$0)
              (sorted_set_c$0 data$0 next$0 lst$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 curr_2$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 curr_2$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 curr_2$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 null$0)))
            (not
                 (member (read$0 data$0 curr_2$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 null$0)))))
   :named sorted_set_2))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 prev_2$0)
                (sorted_set_c$0 data$0 next$0 lst$0 null$0))
              null$0)
            (member (read$0 data$0 prev_2$0)
              (sorted_set_c$0 data$0 next$0 lst$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 prev_2$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 prev_2$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 prev_2$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 null$0)))
            (not
                 (member (read$0 data$0 prev_2$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 null$0)))))
   :named sorted_set_2_1))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l1$0)
                (sorted_set_c$0 data$0 next$0 lst$0 null$0))
              null$0)
            (member (read$0 data$0 sk_l1$0)
              (sorted_set_c$0 data$0 next$0 lst$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l1$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l1$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l1$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 null$0)))
            (not
                 (member (read$0 data$0 sk_l1$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 null$0)))))
   :named sorted_set_2_2))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l1_1$0)
                (sorted_set_c$0 data$0 next$0 lst$0 null$0))
              null$0)
            (member (read$0 data$0 sk_l1_1$0)
              (sorted_set_c$0 data$0 next$0 lst$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l1_1$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l1_1$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l1_1$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 null$0)))
            (not
                 (member (read$0 data$0 sk_l1_1$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 null$0)))))
   :named sorted_set_2_3))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l2$0)
                (sorted_set_c$0 data$0 next$0 lst$0 null$0))
              null$0)
            (member (read$0 data$0 sk_l2$0)
              (sorted_set_c$0 data$0 next$0 lst$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l2$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l2$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l2$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 null$0)))
            (not
                 (member (read$0 data$0 sk_l2$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 null$0)))))
   :named sorted_set_2_4))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l2_1$0)
                (sorted_set_c$0 data$0 next$0 lst$0 null$0))
              null$0)
            (member (read$0 data$0 sk_l2_1$0)
              (sorted_set_c$0 data$0 next$0 lst$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l2_1$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l2_1$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l2_1$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 null$0)))
            (not
                 (member (read$0 data$0 sk_l2_1$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 null$0)))))
   :named sorted_set_2_5))

(assert (! (and
        (or
            (=
              (witness$0 sk_?e$0 (sorted_set_c$0 data$0 next$0 lst$0 null$0))
              null$0)
            (member sk_?e$0 (sorted_set_c$0 data$0 next$0 lst$0 null$0)))
        (or
            (and
                 (= sk_?e$0
                   (read$0 data$0
                     (witness$0 sk_?e$0
                       (sorted_set_c$0 data$0 next$0 lst$0 null$0))))
                 (member
                   (witness$0 sk_?e$0
                     (sorted_set_c$0 data$0 next$0 lst$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 null$0)))
            (not (member sk_?e$0 (sorted_set_c$0 data$0 next$0 lst$0 null$0)))))
   :named sorted_set_2_6))

(assert (! (and
        (or
            (=
              (witness$0 sk_?e_3$0
                (sorted_set_c$0 data$0 next$0 lst$0 null$0))
              null$0)
            (member sk_?e_3$0 (sorted_set_c$0 data$0 next$0 lst$0 null$0)))
        (or
            (and
                 (= sk_?e_3$0
                   (read$0 data$0
                     (witness$0 sk_?e_3$0
                       (sorted_set_c$0 data$0 next$0 lst$0 null$0))))
                 (member
                   (witness$0 sk_?e_3$0
                     (sorted_set_c$0 data$0 next$0 lst$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 null$0)))
            (not (member sk_?e_3$0 (sorted_set_c$0 data$0 next$0 lst$0 null$0)))))
   :named sorted_set_2_7))

(assert (! (forall ((l1 Loc))
           (or (= l1 null$0)
               (member (read$0 data$0 l1)
                 (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
               (not (Btwn$0 next$0 curr_2$0 l1 null$0))))
   :named sorted_set_1_1))

(assert (! (forall ((l1 Loc))
           (or (= l1 curr_2$0)
               (member (read$0 data$0 l1)
                 (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
               (not (Btwn$0 next$0 lst$0 l1 curr_2$0))))
   :named sorted_set_1_2))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 curr_2$0)
                (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
              null$0)
            (member (read$0 data$0 curr_2$0)
              (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 curr_2$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 curr_2$0)
                       (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 curr_2$0)
                     (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0)))
            (not
                 (member (read$0 data$0 curr_2$0)
                   (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))))
   :named sorted_set_2_8))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 prev_2$0)
                (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
              null$0)
            (member (read$0 data$0 prev_2$0)
              (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 prev_2$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 prev_2$0)
                       (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 prev_2$0)
                     (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0)))
            (not
                 (member (read$0 data$0 prev_2$0)
                   (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))))
   :named sorted_set_2_9))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l1$0)
                (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
              null$0)
            (member (read$0 data$0 sk_l1$0)
              (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l1$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l1$0)
                       (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l1$0)
                     (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0)))
            (not
                 (member (read$0 data$0 sk_l1$0)
                   (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))))
   :named sorted_set_2_10))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l1_1$0)
                (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
              null$0)
            (member (read$0 data$0 sk_l1_1$0)
              (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l1_1$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l1_1$0)
                       (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l1_1$0)
                     (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0)))
            (not
                 (member (read$0 data$0 sk_l1_1$0)
                   (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))))
   :named sorted_set_2_11))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l2$0)
                (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
              null$0)
            (member (read$0 data$0 sk_l2$0)
              (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l2$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l2$0)
                       (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l2$0)
                     (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0)))
            (not
                 (member (read$0 data$0 sk_l2$0)
                   (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))))
   :named sorted_set_2_12))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l2_1$0)
                (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
              null$0)
            (member (read$0 data$0 sk_l2_1$0)
              (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l2_1$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l2_1$0)
                       (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l2_1$0)
                     (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0)))
            (not
                 (member (read$0 data$0 sk_l2_1$0)
                   (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))))
   :named sorted_set_2_13))

(assert (! (and
        (or
            (=
              (witness$0 sk_?e$0
                (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
              null$0)
            (member sk_?e$0 (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))
        (or
            (and
                 (= sk_?e$0
                   (read$0 data$0
                     (witness$0 sk_?e$0
                       (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
                 (member
                   (witness$0 sk_?e$0
                     (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0)))
            (not (member sk_?e$0 (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))))
   :named sorted_set_2_14))

(assert (! (and
        (or
            (=
              (witness$0 sk_?e_3$0
                (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
              null$0)
            (member sk_?e_3$0 (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))
        (or
            (and
                 (= sk_?e_3$0
                   (read$0 data$0
                     (witness$0 sk_?e_3$0
                       (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
                 (member
                   (witness$0 sk_?e_3$0
                     (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
                   (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0)))
            (not
                 (member sk_?e_3$0
                   (sorted_set_c$0 data$0 next$0 curr_2$0 null$0)))))
   :named sorted_set_2_15))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 curr_2$0)
                (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
              null$0)
            (member (read$0 data$0 curr_2$0)
              (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))
        (or
            (and
                 (= (read$0 data$0 curr_2$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 curr_2$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))))
                 (member
                   (witness$0 (read$0 data$0 curr_2$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0)))
            (not
                 (member (read$0 data$0 curr_2$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))))
   :named sorted_set_2_16))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 prev_2$0)
                (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
              null$0)
            (member (read$0 data$0 prev_2$0)
              (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))
        (or
            (and
                 (= (read$0 data$0 prev_2$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 prev_2$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))))
                 (member
                   (witness$0 (read$0 data$0 prev_2$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0)))
            (not
                 (member (read$0 data$0 prev_2$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))))
   :named sorted_set_2_17))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l1$0)
                (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
              null$0)
            (member (read$0 data$0 sk_l1$0)
              (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l1$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l1$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l1$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0)))
            (not
                 (member (read$0 data$0 sk_l1$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))))
   :named sorted_set_2_18))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l1_1$0)
                (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
              null$0)
            (member (read$0 data$0 sk_l1_1$0)
              (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l1_1$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l1_1$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l1_1$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0)))
            (not
                 (member (read$0 data$0 sk_l1_1$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))))
   :named sorted_set_2_19))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l2$0)
                (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
              null$0)
            (member (read$0 data$0 sk_l2$0)
              (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l2$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l2$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l2$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0)))
            (not
                 (member (read$0 data$0 sk_l2$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))))
   :named sorted_set_2_20))

(assert (! (and
        (or
            (=
              (witness$0 (read$0 data$0 sk_l2_1$0)
                (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
              null$0)
            (member (read$0 data$0 sk_l2_1$0)
              (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))
        (or
            (and
                 (= (read$0 data$0 sk_l2_1$0)
                   (read$0 data$0
                     (witness$0 (read$0 data$0 sk_l2_1$0)
                       (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))))
                 (member
                   (witness$0 (read$0 data$0 sk_l2_1$0)
                     (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0)))
            (not
                 (member (read$0 data$0 sk_l2_1$0)
                   (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))))
   :named sorted_set_2_21))

(assert (! (and
        (or
            (=
              (witness$0 sk_?e$0
                (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
              null$0)
            (member sk_?e$0 (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))
        (or
            (and
                 (= sk_?e$0
                   (read$0 data$0
                     (witness$0 sk_?e$0
                       (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))))
                 (member
                   (witness$0 sk_?e$0
                     (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0)))
            (not (member sk_?e$0 (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))))
   :named sorted_set_2_22))

(assert (! (and
        (or
            (=
              (witness$0 sk_?e_3$0
                (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
              null$0)
            (member sk_?e_3$0 (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))
        (or
            (and
                 (= sk_?e_3$0
                   (read$0 data$0
                     (witness$0 sk_?e_3$0
                       (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))))
                 (member
                   (witness$0 sk_?e_3$0
                     (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
                   (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0)))
            (not
                 (member sk_?e_3$0 (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0)))))
   :named sorted_set_2_23))

(assert (! (= (read$1 next$0 null$0) null$0) :named read_null))

(assert (! (forall ((l1 Loc))
           (or
               (and (Btwn$0 next$0 lst$0 l1 null$0)
                    (member l1 (sorted_set_domain$0 data$0 next$0 lst$0 null$0))
                    (not (= l1 null$0)))
               (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                    (not
                         (member l1
                           (sorted_set_domain$0 data$0 next$0 lst$0 null$0))))))
   :named sorted_set_footprint))

(assert (! (or (member sk_?e_3$0 c2_2$0)
       (and (member sk_?e_2$0 sk_FP_1$0) (not (member sk_?e_2$0 FP$0)))
       (and (member sk_?e_3$0 (union c1_2$0 c2_2$0))
            (not (member sk_?e_3$0 content$0)))
       (and (member sk_?e_3$0 c1_2$0)
            (not
                 (member sk_?e_3$0
                   (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
       (and (member sk_?e_3$0 content$0)
            (not (member sk_?e_3$0 (union c1_2$0 c2_2$0))))
       (and (member sk_?e_3$0 (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
            (not (member sk_?e_3$0 c1_2$0)))
       (and (not (= curr_2$0 null$0)) (not (= prev_2$0 null$0))
            (not (< (read$0 data$0 prev_2$0) (read$0 data$0 curr_2$0))))
       (not (= curr_2$0 lst$0)) (not (= prev_2$0 null$0))
       (not
            (sorted_set_struct$0 sk_?X_3$0 data$0 next$0 curr_2$0 null$0
              c1_2$0)))
   :named invariant_37_2))

(assert (! (= sk_FP_1$0 sk_?X_2$0) :named invariant_37_2_1))

(assert (! (= sk_?X_5$0 (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0))
   :named invariant_37_2_2))

(assert (! (= sk_?X_3$0 (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0))
   :named invariant_37_2_3))

(assert (! (= sk_?X_1$0 (union sk_?X_3$0 sk_?X_4$0)) :named invariant_37_2_4))

(assert (! (= FP_Caller$0 (union FP$0 FP_Caller$0))
   :named precondition_of_insert_27_11))

(assert (! (= sk_?X$0 FP$0) :named precondition_of_insert_27_11_1))

(assert (! (= Alloc$0 (union FP_Caller$0 Alloc$0))
   :named initial_footprint_of_insert_27_11))

(assert (! (= curr_2$0 lst$0) :named assign_31_2))

(assert (! (= c1_2$0 content$0) :named assign_34_2))

(assert (! (or (and (Btwn$0 next$0 lst$0 null$0 null$0) Axiom$0)
       (not
            (sorted_set_struct$0 sk_?X$0 data$0 next$0 lst$0 null$0
              content$0)))
   :named unnamed))

(assert (! (or (sorted_set_struct$0 sk_?X_3$0 data$0 next$0 curr_2$0 null$0 c1_2$0)
       (not (Btwn$0 next$0 curr_2$0 null$0 null$0))
       (! (and (Btwn$0 next$0 sk_l1$0 sk_l2$0 null$0) (member sk_l1$0 sk_?X_3$0)
               (member sk_l2$0 sk_?X_3$0) (not (= sk_l1$0 sk_l2$0))
               (not (< (read$0 data$0 sk_l1$0) (read$0 data$0 sk_l2$0))))
          :named strict_sortedness_1))
   :named unnamed_1))

(assert (! (forall ((l1 Loc))
           (or
               (and (Btwn$0 next$0 lst$0 l1 curr_2$0)
                    (member l1
                      (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0))
                    (not (= l1 curr_2$0)))
               (and
                    (or (= l1 curr_2$0)
                        (not (Btwn$0 next$0 lst$0 l1 curr_2$0)))
                    (not
                         (member l1
                           (sorted_set_domain$0 data$0 next$0 lst$0 curr_2$0))))))
   :named sorted_set_footprint_1))

(assert (! (forall ((l1 Loc))
           (or
               (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                    (member l1
                      (sorted_set_domain$0 data$0 next$0 curr_2$0 null$0))
                    (not (= l1 null$0)))
               (and
                    (or (= l1 null$0)
                        (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                    (not
                         (member l1
                           (sorted_set_domain$0 data$0 next$0 curr_2$0
                             null$0))))))
   :named sorted_set_footprint_2))

(assert (! (not (member null$0 Alloc$0)) :named initial_footprint_of_insert_27_11_1))

(assert (! (or (= prev_2$0 curr_2$0)
       (member sk_?e_1$0 (intersection sk_?X_4$0 sk_?X_3$0))
       (and (member sk_?e_1$0 sk_FP$0) (not (member sk_?e_1$0 FP$0)))
       (and (member sk_?e$0 (union c1_2$0 c2_2$0)) (not (member sk_?e$0 content$0)))
       (and (member sk_?e$0 c1_2$0)
            (not (member sk_?e$0 (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))))
       (and (member sk_?e$0 c2_2$0)
            (not (member sk_?e$0 (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))))
       (and (member sk_?e$0 content$0) (not (member sk_?e$0 (union c1_2$0 c2_2$0))))
       (and (member sk_?e$0 (sorted_set_c$0 data$0 next$0 curr_2$0 null$0))
            (not (member sk_?e$0 c1_2$0)))
       (and (member sk_?e$0 (sorted_set_c$0 data$0 next$0 lst$0 curr_2$0))
            (not (member sk_?e$0 c2_2$0)))
       (and (not (= curr_2$0 null$0)) (not (= prev_2$0 null$0))
            (not (< (read$0 data$0 prev_2$0) (read$0 data$0 curr_2$0))))
       (not (= (read$1 next$0 prev_2$0) curr_2$0))
       (not (> val$0 (read$0 data$0 prev_2$0)))
       (not (Btwn$0 next$0 lst$0 prev_2$0 curr_2$0))
       (not
            (sorted_set_struct$0 sk_?X_3$0 data$0 next$0 curr_2$0 null$0
              c1_2$0))
       (not
            (sorted_set_struct$0 sk_?X_5$0 data$0 next$0 lst$0 curr_2$0
              c2_2$0)))
   :named invariant_37_2_5))

(assert (! (= sk_FP$0 sk_?X_1$0) :named invariant_37_2_6))

(assert (! (= sk_?X_4$0 sk_?X_5$0) :named invariant_37_2_7))

(assert (! (= sk_?X_2$0 sk_?X_3$0) :named invariant_37_2_8))

(assert (! (sorted_set_struct$0 sk_?X$0 data$0 next$0 lst$0 null$0 content$0)
   :named precondition_of_insert_27_11_2))

(assert (! (= sk_?X$0 (sorted_set_domain$0 data$0 next$0 lst$0 null$0))
   :named precondition_of_insert_27_11_3))

(assert (! (= content$0 (sorted_set_c$0 data$0 next$0 lst$0 null$0))
   :named precondition_of_insert_27_11_4))

(assert (! (= prev_2$0 null$0) :named assign_32_2))

(assert (! (= c2_2$0 (as emptyset SetInt)) :named assign_35_2))

(assert (! (= FP_Caller_1$0 (setminus FP_Caller$0 FP$0)) :named assign_29_0))

(assert (! (or (sorted_set_struct$0 sk_?X_5$0 data$0 next$0 lst$0 curr_2$0 c2_2$0)
       (not (Btwn$0 next$0 lst$0 curr_2$0 curr_2$0))
       (! (and (Btwn$0 next$0 sk_l1_1$0 sk_l2_1$0 curr_2$0)
               (member sk_l1_1$0 sk_?X_5$0) (member sk_l2_1$0 sk_?X_5$0)
               (not (= sk_l1_1$0 sk_l2_1$0))
               (not (< (read$0 data$0 sk_l1_1$0) (read$0 data$0 sk_l2_1$0))))
          :named strict_sortedness_2))
   :named unnamed_2))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named btwn_refl))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y)))
   :named btwn_sndw))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
               (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y)))
   :named btwn_ord1))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?z))
               (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z))))
   :named btwn_ord2))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
               (Btwn$0 next$0 ?x ?z ?z)))
   :named btwn_trn1))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
               (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z))))
   :named btwn_trn2))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
           (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
               (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z))))
   :named btwn_trn3))

(check-sat)
(exit)
