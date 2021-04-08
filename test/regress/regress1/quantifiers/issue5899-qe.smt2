; SCRUBBER: sed 's/(.*)/()/g'
; EXPECT: ()
; EXIT: 0


(set-logic LIRA)
(define-fun
 __node_init_HH_4
 ((HH.usr.x@0 Bool)
  (HH.usr.y@0 Bool)
  (HH.res.init_flag@0 Bool))
 Bool
 (and
  (= HH.usr.y@0 HH.usr.x@0)
  HH.res.init_flag@0))
;; Success 

(define-fun
 __node_trans_HH_4
 ((HH.usr.x@1 Bool)
  (HH.usr.y@1 Bool)
  (HH.res.init_flag@1 Bool)
  (HH.usr.x@0 Bool)
  (HH.usr.y@0 Bool)
  (HH.res.init_flag@0 Bool))
 Bool
 (and
  (= HH.usr.y@1 (or HH.usr.x@1 HH.usr.y@0))
  (not HH.res.init_flag@1)))
;; Success 

(define-fun
 __node_init_FTH_4
 ((FTH.usr.x@0 Bool)
  (FTH.usr.r@0 Bool)
  (FTH.res.init_flag@0 Bool)
  (FTH.res.abs_0@0 Bool)
  (FTH.res.inst_1@0 Bool))
 Bool
 (and
  (= FTH.usr.r@0 FTH.usr.x@0)
  (__node_init_HH_4
   FTH.usr.x@0
   FTH.res.abs_0@0
   FTH.res.inst_1@0)
  FTH.res.init_flag@0))
;; Success 

(define-fun
 __node_trans_FTH_4
 ((FTH.usr.x@1 Bool)
  (FTH.usr.r@1 Bool)
  (FTH.res.init_flag@1 Bool)
  (FTH.res.abs_0@1 Bool)
  (FTH.res.inst_1@1 Bool)
  (FTH.usr.x@0 Bool)
  (FTH.usr.r@0 Bool)
  (FTH.res.init_flag@0 Bool)
  (FTH.res.abs_0@0 Bool)
  (FTH.res.inst_1@0 Bool))
 Bool
 (and
  (=
   FTH.usr.r@1
   (and (not FTH.res.abs_0@0) FTH.usr.x@1))
  (__node_trans_HH_4
   FTH.usr.x@1
   FTH.res.abs_0@1
   FTH.res.inst_1@1
   FTH.usr.x@0
   FTH.res.abs_0@0
   FTH.res.inst_1@0)
  (not FTH.res.init_flag@1)))
;; Success 

(declare-fun %f137@0 () Bool)
;; Success 

(declare-fun %f144@0 () Bool)
;; Success 

(declare-fun %f145@0 () Real)
;; Success 

(declare-fun %f146@0 () Real)
;; Success 

(declare-fun %f147@0 () Int)
;; Success 

(declare-fun %f148@0 () Real)
;; Success 

(declare-fun %f149@0 () Real)
;; Success 

(declare-fun %f136@0 () Bool)
;; Success 

(declare-fun %f150@0 () Bool)
;; Success 

(declare-fun %f151@0 () Bool)
;; Success 

(declare-fun %f152@0 () Bool)
;; Success 

(declare-fun %f154@0 () Bool)
;; Success 

(declare-fun %f155@0 () Bool)
;; Success 

(declare-fun %f156@0 () Bool)
;; Success 

(declare-fun %f157@0 () Bool)
;; Success 

(declare-fun %f158@0 () Bool)
;; Success 

(declare-fun %f275@0 () Bool)
;; Success 

(declare-fun %f274@0 () Bool)
;; Success 

(declare-fun %f273@0 () Bool)
;; Success 

(declare-fun %f272@0 () Bool)
;; Success 

(declare-fun %f271@0 () Bool)
;; Success 

(declare-fun %f137@1 () Bool)
;; Success 

(declare-fun %f144@1 () Bool)
;; Success 

(declare-fun %f145@1 () Real)
;; Success 

(declare-fun %f146@1 () Real)
;; Success 

(declare-fun %f147@1 () Int)
;; Success 

(declare-fun %f148@1 () Real)
;; Success 

(declare-fun %f149@1 () Real)
;; Success 

(declare-fun %f136@1 () Bool)
;; Success 

(declare-fun %f150@1 () Bool)
;; Success 

(declare-fun %f151@1 () Bool)
;; Success 

(declare-fun %f152@1 () Bool)
;; Success 

(declare-fun %f154@1 () Bool)
;; Success 

(declare-fun %f155@1 () Bool)
;; Success 

(declare-fun %f156@1 () Bool)
;; Success 

(declare-fun %f157@1 () Bool)
;; Success 

(declare-fun %f158@1 () Bool)
;; Success 

(declare-fun %f275@1 () Bool)
;; Success 

(declare-fun %f274@1 () Bool)
;; Success 

(declare-fun %f273@1 () Bool)
;; Success 

(declare-fun %f272@1 () Bool)
;; Success 

(declare-fun %f271@1 () Bool)
;; Success

(get-qe
 (exists
 ((X1 Bool)
  (X2 Bool)
  (X3 Bool)
  (X4 Bool)
  (X5 Bool)
  (X6 Bool)
  (X7 Bool)
  (X8 Bool)
  (X9 Bool)
  (X10 Bool)
  (X11 Bool)
  (X12 Bool)
  (X13 Bool)
  (X14 Bool)
  (X15 Real)
  (X16 Real)
  (X17 Int)
  (X18 Real)
  (X19 Real)
  (X20 Bool)
  (X21 Bool))
  (not
   (or
    (and
     (or X21 (not X20))
     (or
      (and
       (not %f150@0)
       (or
        (__node_trans_FTH_4
         false
         false
         false
         true
         false
         false
         %f154@0
         %f274@0
         %f273@0
         %f272@0)
        (__node_trans_FTH_4
         false
         false
         false
         false
         false
         false
         %f154@0
         %f274@0
         %f273@0
         %f272@0))
       (or
        (__node_trans_HH_4 false true false false %f151@0 %f275@0)
        (__node_trans_HH_4 false false false false %f151@0 %f275@0))
       (or
        (__node_trans_HH_4 false true false %f156@0 %f157@0 %f271@0)
        (__node_trans_HH_4
         false
         false
         false
         %f156@0
         %f157@0
         %f271@0)))
      (and
       %f150@0
       (__node_trans_HH_4 true true false %f156@0 %f157@0 %f271@0)
       (or
        (__node_trans_FTH_4
         false
         false
         false
         true
         false
         true
         %f154@0
         %f274@0
         %f273@0
         %f272@0)
        (__node_trans_FTH_4
         false
         false
         false
         false
         false
         true
         %f154@0
         %f274@0
         %f273@0
         %f272@0))
       (or
        (__node_trans_HH_4 false true false true %f151@0 %f275@0)
        (__node_trans_HH_4 false false false true %f151@0 %f275@0)))))
    (and
     X20
     (not X21)
     (or
      (and
       (not %f150@0)
       (__node_trans_HH_4 true true false false %f151@0 %f275@0)
       (or
        (and
         (__node_trans_HH_4
          false
          true
          false
          %f156@0
          %f157@0
          %f271@0)
         (or
          (__node_trans_FTH_4
           true
           false
           false
           true
           false
           false
           %f154@0
           %f274@0
           %f273@0
           %f272@0)
          (and
           (= %f148@0 X19)
           (= %f149@0 X18)
           (__node_trans_FTH_4
            true
            true
            false
            true
            false
            false
            %f154@0
            %f274@0
            %f273@0
            %f272@0))))
        (and
         (__node_trans_HH_4
          false
          false
          false
          %f156@0
          %f157@0
          %f271@0)
         (or
          (__node_trans_FTH_4
           true
           true
           false
           true
           false
           false
           %f154@0
           %f274@0
           %f273@0
           %f272@0)
          (__node_trans_FTH_4
           true
           false
           false
           true
           false
           false
           %f154@0
           %f274@0
           %f273@0
           %f272@0)))))
      (and
       %f150@0
       (__node_trans_HH_4 true true false %f156@0 %f157@0 %f271@0)
       (__node_trans_HH_4 true true false true %f151@0 %f275@0)
       (or
        (__node_trans_FTH_4
         true
         false
         false
         true
         false
         true
         %f154@0
         %f274@0
         %f273@0
         %f272@0)
        (and
         (= %f148@0 X19)
         (= %f149@0 X18)
         (__node_trans_FTH_4
          true
          true
          false
          true
          false
          true
          %f154@0
          %f274@0
          %f273@0
          %f272@0))))))))))

(exit)
;; NoResponse 

