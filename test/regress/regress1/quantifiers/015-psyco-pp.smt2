(set-info :smt-lib-version 2.6)
(set-logic LIA)
(set-info :status sat)
(declare-fun R_S1_V5 () Bool)
(declare-fun W_S2_V5 () Bool)
(declare-fun W_S2_V3 () Bool)
(declare-fun W_S1_V5 () Bool)
(declare-fun R_S2_V1 () Bool)
(declare-fun W_S1_V1 () Bool)
(declare-fun R_S2_V3 () Bool)
(declare-fun R_S2_V2 () Bool)
(declare-fun W_S1_V2 () Bool)
(declare-fun R_S2_V5 () Bool)
(declare-fun R_S1_V1 () Bool)
(declare-fun R_S1_V3 () Bool)
(declare-fun R_S1_V2 () Bool)
(declare-fun R_S2_V4 () Bool)
(declare-fun DISJ_W_S2_R_S2 () Bool)
(declare-fun R_S1_V4 () Bool)
(declare-fun W_S1_V4 () Bool)
(declare-fun DISJ_W_S1_R_S1 () Bool)
(declare-fun W_S2_V4 () Bool)
(declare-fun W_S1_V3 () Bool)
(declare-fun W_S2_V1 () Bool)
(declare-fun W_S2_V2 () Bool)
(declare-fun DISJ_W_S2_R_S1 () Bool)
(declare-fun DISJ_W_S1_W_S2 () Bool)
(declare-fun DISJ_W_S1_R_S2 () Bool)
(assert
 (let (($x796 (not W_S2_V3)))
 (let (($x177 (not R_S2_V3)))
 (let
 (($x1274
   (forall
    ((V4_0 Int) (V5_0 Int) 
     (V2_0 Int) (V3_0 Int) 
     (V1_0 Int) (MW_S1_V4 Bool) 
     (MW_S1_V5 Bool) (MW_S1_V2 Bool) 
     (MW_S1_V3 Bool) (MW_S1_V1 Bool) 
     (MW_S2_V4 Bool) (MW_S2_V5 Bool) 
     (MW_S2_V2 Bool) (MW_S2_V3 Bool) 
     (MW_S2_V1 Bool) (S1_V4_!5047 Int) 
     (S1_V4_!5057 Int) (S1_V4_!5072 Int) 
     (S1_V4_!5077 Int) (S2_V4_!5052 Int) 
     (S2_V4_!5062 Int) (S2_V4_!5067 Int) 
     (S2_V5_!5053 Int) (S2_V5_!5063 Int) 
     (S2_V5_!5068 Int) (S1_V1_!5051 Int) 
     (S1_V1_!5061 Int) (S1_V1_!5076 Int) 
     (S1_V1_!5081 Int) (S1_V3_!5050 Int) 
     (S1_V3_!5060 Int) (S1_V3_!5075 Int) 
     (S1_V3_!5080 Int) (S1_V2_!5049 Int) 
     (S1_V2_!5059 Int) (S1_V2_!5074 Int) 
     (S1_V2_!5079 Int) (S2_V1_!5056 Int) 
     (S2_V1_!5066 Int) (S2_V1_!5071 Int) 
     (S2_V2_!5054 Int) (S2_V2_!5064 Int) 
     (S2_V2_!5069 Int) (S2_V3_!5055 Int) 
     (S2_V3_!5065 Int) (S2_V3_!5070 Int) 
     (S1_V5_!5048 Int) (S1_V5_!5058 Int) 
     (S1_V5_!5073 Int) (S1_V5_!5078 Int))
    (let ((?x19858 (ite MW_S1_V1 S1_V1_!5051 V1_0)))
    (let ((?x19735 (ite MW_S2_V1 S2_V1_!5056 ?x19858)))
    (let ((?x2666 (+ 1 ?x19735)))
    (let ((?x19816 (ite MW_S1_V1 S1_V1_!5061 ?x2666)))
    (let
    (($x19044
      (= (ite MW_S2_V1 S2_V1_!5066 ?x19816)
      (ite MW_S1_V1 S1_V1_!5081
      (+ 1 (ite MW_S1_V1 S1_V1_!5076 (ite MW_S2_V1 S2_V1_!5071 V1_0)))))))
    (let
    (($x20397
      (=
      (ite MW_S2_V3 S2_V3_!5065
      (ite MW_S1_V3 S1_V3_!5060
      (ite MW_S2_V3 S2_V3_!5055 (ite MW_S1_V3 S1_V3_!5050 V3_0))))
      (ite MW_S1_V3 S1_V3_!5080 (ite MW_S2_V3 S2_V3_!5070 V3_0)))))
    (let
    (($x19931
      (=
      (ite MW_S2_V2 S2_V2_!5064
      (ite MW_S1_V2 S1_V2_!5059
      (ite MW_S2_V2 S2_V2_!5054 (ite MW_S1_V2 S1_V2_!5049 V2_0))))
      (ite MW_S1_V2 S1_V2_!5079 (ite MW_S2_V2 S2_V2_!5069 V2_0)))))
    (let
    (($x19917
      (=
      (ite MW_S2_V5 S2_V5_!5063
      (ite MW_S1_V5 S1_V5_!5058
      (ite MW_S2_V5 S2_V5_!5053 (ite MW_S1_V5 S1_V5_!5048 V5_0))))
      (ite MW_S1_V5 S1_V5_!5078 (ite MW_S2_V5 S2_V5_!5068 V5_0)))))
    (let
    (($x19951
      (=
      (ite MW_S2_V4 S2_V4_!5062
      (ite MW_S1_V4 S1_V4_!5057
      (ite MW_S2_V4 S2_V4_!5052 (ite MW_S1_V4 S1_V4_!5047 V4_0))))
      (ite MW_S1_V4 S1_V4_!5077 (ite MW_S2_V4 S2_V4_!5067 V4_0)))))
    (let
    (($x19175
      (>=
      (ite MW_S1_V1 S1_V1_!5081
      (+ 1 (ite MW_S1_V1 S1_V1_!5076 (ite MW_S2_V1 S2_V1_!5071 V1_0))))
      (+ (- 1) (ite MW_S1_V2 S1_V2_!5079 (ite MW_S2_V2 S2_V2_!5069 V2_0))))))
    (let ((?x19970 (ite MW_S2_V1 S2_V1_!5071 V1_0)))
    (let ((?x19876 (ite MW_S1_V1 S1_V1_!5076 ?x19970)))
    (let ((?x20041 (+ 1 ?x19876)))
    (let ((?x20154 (ite MW_S2_V2 S2_V2_!5069 V2_0)))
    (let ((?x20275 (ite MW_S1_V2 S1_V2_!5074 ?x20154)))
    (let
    ((?x20280
      (+ (- 1)
      (ite MW_S2_V2 S2_V2_!5064
      (ite MW_S1_V2 S1_V2_!5059
      (ite MW_S2_V2 S2_V2_!5054 (ite MW_S1_V2 S1_V2_!5049 V2_0)))))))
    (let
    (($x20340
      (and (not (<= V2_0 V1_0))
      (not
      (<= (ite MW_S2_V2 S2_V2_!5054 (ite MW_S1_V2 S1_V2_!5049 V2_0)) ?x2666))
      (>= (ite MW_S2_V1 S2_V1_!5066 ?x19816) ?x20280)
      (not (<= ?x20154 ?x19970)) 
      (not (<= ?x20275 ?x20041)) $x19175)))
    (let (($x164 (not R_S1_V3)))
    (let
    (($x16591
      (or $x164
      (= (ite MW_S1_V3 S1_V3_!5075 (ite MW_S2_V3 S2_V3_!5070 V3_0))
      (ite MW_S2_V3 S2_V3_!5070 V3_0)))))
    (let (($x160 (not R_S1_V5)))
    (let
    (($x4147
      (or $x160
      (= (ite MW_S1_V5 S1_V5_!5073 (ite MW_S2_V5 S2_V5_!5068 V5_0))
      (ite MW_S2_V5 S2_V5_!5068 V5_0)))))
    (let
    (($x20079
      (and $x4147 (or (not R_S1_V2) (= ?x20275 ?x20154)) $x16591
      (or (not R_S1_V1) (= ?x19876 (+ (- 1) ?x19970))))))
    (let (($x1365 (not $x20079)))
    (let ((?x19329 (ite MW_S2_V3 S2_V3_!5070 V3_0)))
    (let ((?x20227 (ite MW_S1_V3 S1_V3_!5075 ?x19329)))
    (let
    ((?x19017 (ite MW_S2_V3 S2_V3_!5055 (ite MW_S1_V3 S1_V3_!5050 V3_0))))
    (let ((?x19159 (ite MW_S2_V5 S2_V5_!5068 V5_0)))
    (let ((?x19823 (ite MW_S1_V5 S1_V5_!5073 ?x19159)))
    (let ((?x19445 (ite MW_S1_V5 S1_V5_!5048 V5_0)))
    (let ((?x19140 (ite MW_S2_V5 S2_V5_!5053 ?x19445)))
    (let
    (($x20082
      (and (or $x160 (= ?x19140 ?x19823))
      (or (not R_S1_V2)
      (= (ite MW_S2_V2 S2_V2_!5054 (ite MW_S1_V2 S1_V2_!5049 V2_0)) ?x20275))
      (or $x164 (= ?x19017 ?x20227)) 
      (or (not R_S1_V1) (= ?x19735 ?x19876)))))
    (let (($x20074 (not $x20082)))
    (let
    (($x20083
      (and (or $x160 (= ?x19140 ?x19159))
      (or (not R_S1_V2)
      (= (ite MW_S2_V2 S2_V2_!5054 (ite MW_S1_V2 S1_V2_!5049 V2_0)) ?x20154))
      (or $x164 (= ?x19017 ?x19329))
      (or (not R_S1_V1) (= ?x19735 (+ (- 1) ?x19970))))))
    (let (($x20084 (not $x20083)))
    (let
    (($x8373
      (and (or $x160 (= ?x19140 V5_0))
      (or (not R_S1_V2)
      (= (ite MW_S2_V2 S2_V2_!5054 (ite MW_S1_V2 S1_V2_!5049 V2_0)) V2_0))
      (or $x164 (= ?x19017 V3_0))
      (or (not R_S1_V1) (= ?x19735 (+ (- 1) V1_0))))))
    (let (($x19787 (not $x8373)))
    (let
    (($x19719
      (and (or $x160 (= V5_0 ?x19823)) 
      (or (not R_S1_V2) (= V2_0 ?x20275)) 
      (or $x164 (= V3_0 ?x20227)) 
      (or (not R_S1_V1) (= V1_0 ?x20041)))))
    (let (($x19712 (not $x19719)))
    (let
    (($x1403
      (and (or $x160 (= V5_0 ?x19159)) 
      (or (not R_S1_V2) (= V2_0 ?x20154)) 
      (or $x164 (= V3_0 ?x19329)) 
      (or (not R_S1_V1) (= V1_0 ?x19970)))))
    (let (($x1473 (not $x1403)))
    (let
    (($x20361
      (and (or (not R_S2_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!5047 V4_0)))
      (or (not R_S2_V5) (= V5_0 ?x19445))
      (or (not R_S2_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!5049 V2_0)))
      (or (not R_S2_V1) (= V1_0 ?x19858)))))
    (let (($x19974 (not $x20361)))
    (let (($x175 (not R_S2_V2)))
    (let
    (($x19080
      (or $x175
      (=
      (ite MW_S1_V2 S1_V2_!5059
      (ite MW_S2_V2 S2_V2_!5054 (ite MW_S1_V2 S1_V2_!5049 V2_0))) V2_0))))
    (let (($x171 (not R_S2_V4)))
    (let
    (($x1175
      (or $x171
      (=
      (ite MW_S1_V4 S1_V4_!5057
      (ite MW_S2_V4 S2_V4_!5052 (ite MW_S1_V4 S1_V4_!5047 V4_0))) V4_0))))
    (let
    (($x19801
      (and $x1175
      (or (not R_S2_V5) (= (ite MW_S1_V5 S1_V5_!5058 ?x19140) V5_0)) $x19080
      (or (not R_S2_V1) (= ?x19816 V1_0)))))
    (let (($x19804 (not $x19801)))
    (let ((?x10718 (ite MW_S1_V2 S1_V2_!5049 V2_0)))
    (let ((?x18681 (ite MW_S2_V2 S2_V2_!5054 ?x10718)))
    (let ((?x19161 (ite MW_S1_V2 S1_V2_!5059 ?x18681)))
    (let ((?x19599 (ite MW_S1_V4 S1_V4_!5047 V4_0)))
    (let
    ((?x18788 (ite MW_S1_V4 S1_V4_!5057 (ite MW_S2_V4 S2_V4_!5052 ?x19599))))
    (let
    (($x3852
      (and (or $x171 (= ?x18788 ?x19599))
      (or (not R_S2_V5) (= (ite MW_S1_V5 S1_V5_!5058 ?x19140) ?x19445))
      (or $x175 (= ?x19161 ?x10718)) 
      (or (not R_S2_V1) (= ?x19816 ?x19858)))))
    (let (($x19708 (not $x3852)))
    (let
    (($x20195
      (and (or $x171 (= V4_0 ?x18788))
      (or (not R_S2_V5) (= V5_0 (ite MW_S1_V5 S1_V5_!5058 ?x19140)))
      (or $x175 (= V2_0 ?x19161)) 
      (or (not R_S2_V1) (= V1_0 ?x19816)))))
    (let
    (($x1440
      (and (or $x160 (= ?x19823 ?x19140))
      (or (not R_S1_V2) (= ?x20275 ?x18681)) 
      (or $x164 (= ?x20227 ?x19017)) 
      (or (not R_S1_V1) (= ?x19876 ?x19735)))))
    (let
    (($x1199
      (and (or $x160 (= ?x19823 V5_0)) 
      (or (not R_S1_V2) (= ?x20275 V2_0)) 
      (or $x164 (= ?x20227 V3_0))
      (or (not R_S1_V1) (= ?x19876 (+ (- 1) V1_0))))))
    (let
    (($x1442
      (and (or $x160 (= ?x19159 ?x19140))
      (or (not R_S1_V2) (= ?x20154 ?x18681)) 
      (or $x164 (= ?x19329 ?x19017)) 
      (or (not R_S1_V1) (= ?x19970 ?x2666)))))
    (let
    (($x1484
      (and (or $x160 (= V5_0 ?x19140)) 
      (or (not R_S1_V2) (= V2_0 ?x18681)) 
      (or $x164 (= V3_0 ?x19017)) 
      (or (not R_S1_V1) (= V1_0 ?x2666)))))
    (let
    (($x19714
      (and (or $x171 (= ?x19599 ?x18788))
      (or (not R_S2_V5) (= ?x19445 (ite MW_S1_V5 S1_V5_!5058 ?x19140)))
      (or $x175 (= ?x10718 ?x19161)) 
      (or (not R_S2_V1) (= ?x19858 ?x19816)))))
    (let
    (($x20189
      (and (or $x160 (= ?x19159 ?x19823))
      (or (not R_S1_V2) (= ?x20154 ?x20275)) 
      (or $x164 (= ?x19329 ?x20227)) 
      (or (not R_S1_V1) (= ?x19970 ?x20041)))))
    (let
    (($x19788
      (and (or $x160 (= ?x19159 V5_0)) 
      (or (not R_S1_V2) (= ?x20154 V2_0)) 
      (or $x164 (= ?x19329 V3_0)) 
      (or (not R_S1_V1) (= ?x19970 V1_0)))))
    (let
    (($x1223
      (and (or $x19712 (= S1_V4_!5047 S1_V4_!5077))
      (or $x19787 (= S1_V4_!5057 S1_V4_!5047))
      (or $x20084 (= S1_V4_!5057 S1_V4_!5072))
      (or $x20074 (= S1_V4_!5057 S1_V4_!5077))
      (or (not $x19788) (= S1_V4_!5072 S1_V4_!5047))
      (or (not $x20189) (= S1_V4_!5072 S1_V4_!5077))
      (or $x19708 (= S2_V4_!5062 S2_V4_!5052))
      (or $x19804 (= S2_V4_!5062 S2_V4_!5067))
      (or $x19974 (= S2_V4_!5067 S2_V4_!5052))
      (or (not $x19714) (= S2_V5_!5053 S2_V5_!5063))
      (or $x19974 (= S2_V5_!5068 S2_V5_!5053))
      (or (not $x20195) (= S2_V5_!5068 S2_V5_!5063))
      (or $x1473 (= S1_V1_!5051 S1_V1_!5076))
      (or $x19712 (= S1_V1_!5051 S1_V1_!5081))
      (or $x19787 (= S1_V1_!5061 S1_V1_!5051))
      (or $x20084 (= S1_V1_!5061 S1_V1_!5076))
      (or $x20074 (= S1_V1_!5061 S1_V1_!5081))
      (or $x1365 (= S1_V1_!5081 S1_V1_!5076))
      (or (not $x1484) (= S1_V3_!5050 S1_V3_!5060))
      (or $x1473 (= S1_V3_!5050 S1_V3_!5075))
      (or $x19712 (= S1_V3_!5050 S1_V3_!5080))
      (or $x20084 (= S1_V3_!5060 S1_V3_!5075))
      (or (not $x1440) (= S1_V3_!5080 S1_V3_!5060))
      (or $x1365 (= S1_V3_!5080 S1_V3_!5075))
      (or (not $x1484) (= S1_V2_!5049 S1_V2_!5059))
      (or $x1473 (= S1_V2_!5049 S1_V2_!5074))
      (or (not $x1442) (= S1_V2_!5074 S1_V2_!5059))
      (or (not $x1199) (= S1_V2_!5079 S1_V2_!5049))
      (or (not $x1440) (= S1_V2_!5079 S1_V2_!5059))
      (or $x1365 (= S1_V2_!5079 S1_V2_!5074))
      (or $x19708 (= S2_V1_!5066 S2_V1_!5056))
      (or $x19974 (= S2_V1_!5071 S2_V1_!5056))
      (or (not $x20195) (= S2_V1_!5071 S2_V1_!5066))
      (or $x19708 (= S2_V2_!5064 S2_V2_!5054))
      (or $x19804 (= S2_V2_!5064 S2_V2_!5069))
      (or $x19974 (= S2_V2_!5069 S2_V2_!5054))
      (or $x19708 (= S2_V3_!5065 S2_V3_!5055))
      (or $x19804 (= S2_V3_!5065 S2_V3_!5070))
      (or $x19974 (= S2_V3_!5070 S2_V3_!5055))
      (or $x1473 (= S1_V5_!5048 S1_V5_!5073))
      (or $x19712 (= S1_V5_!5048 S1_V5_!5078))
      (or $x19787 (= S1_V5_!5058 S1_V5_!5048))
      (or $x20084 (= S1_V5_!5058 S1_V5_!5073))
      (or $x20074 (= S1_V5_!5058 S1_V5_!5078))
      (or $x1365 (= S1_V5_!5078 S1_V5_!5073)) 
      (not MW_S1_V4) (or (not MW_S1_V5) W_S1_V5) 
      (or (not MW_S1_V2) W_S1_V2) 
      (or (not MW_S1_V1) W_S1_V1) 
      (or (not MW_S2_V5) W_S2_V5) 
      (not MW_S2_V2) (not MW_S2_V3) 
      (not MW_S2_V1))))
    (or (not $x1223) (not $x20340)
    (and $x19951 $x19917 $x19931 $x20397 $x19044)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (let (($x158 (not R_S1_V4)))
 (let (($x754 (not W_S1_V4)))
 (let (($x23 (and W_S1_V1 R_S1_V1)))
 (let (($x18 (and W_S1_V2 R_S1_V2)))
 (let (($x15 (and W_S1_V5 R_S1_V5)))
 (let (($x786 (not W_S2_V1)))
 (let (($x783 (not W_S2_V2)))
 (and DISJ_W_S1_R_S2 DISJ_W_S1_W_S2 DISJ_W_S2_R_S1 $x783 $x786 W_S1_V3
 W_S2_V4 (= DISJ_W_S1_R_S1 (not (or $x15 $x18 R_S1_V3 $x23))) $x754 $x158
 (= DISJ_W_S2_R_S2 (not (or R_S2_V4 (and W_S2_V5 R_S2_V5)))) $x1274
 (not (and W_S1_V5 R_S2_V5)) 
 (not (and W_S1_V2 R_S2_V2)) $x177 
 (not (and W_S1_V1 R_S2_V1)) 
 (not (and W_S1_V5 W_S2_V5)) $x796 
 (not (and W_S2_V5 R_S1_V5))))))))))))))
(check-sat)
(exit)
