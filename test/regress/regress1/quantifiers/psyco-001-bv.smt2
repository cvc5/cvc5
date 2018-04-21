(set-logic BV)
(set-info :status sat)
(declare-fun W_S1_V1 () Bool)
(declare-fun W_S1_V2 () Bool)
(declare-fun W_S1_V4 () Bool)
(declare-fun R_S1_V1 () Bool)
(declare-fun R_E1_V1 () Bool)
(declare-fun R_E1_V3 () Bool)
(declare-fun R_E1_V2 () Bool)
(declare-fun R_E1_V4 () Bool)
(declare-fun DISJ_W_S1_R_E1 () Bool)
(declare-fun R_S1_V3 () Bool)
(declare-fun R_S1_V2 () Bool)
(declare-fun R_S1_V4 () Bool)
(declare-fun DISJ_W_S1_R_S1 () Bool)
(declare-fun W_S1_V3 () Bool)
(assert
 (let
 (($x324
   (forall
    ((V4_0 (_ BitVec 32)) (V2_0 (_ BitVec 32)) 
     (V3_0 (_ BitVec 32)) (V1_0 (_ BitVec 32)) 
     (MW_S1_V4 Bool) (MW_S1_V2 Bool) 
     (MW_S1_V3 Bool) (MW_S1_V1 Bool) 
     (S1_V3_!14 (_ BitVec 32)) (S1_V3_!20 (_ BitVec 32)) 
     (E1_!11 (_ BitVec 32)) (E1_!16 (_ BitVec 32)) 
     (E1_!17 (_ BitVec 32)) (S1_V1_!15 (_ BitVec 32)) 
     (S1_V1_!21 (_ BitVec 32)) (S1_V2_!13 (_ BitVec 32)) 
     (S1_V2_!19 (_ BitVec 32)) (S1_V4_!12 (_ BitVec 32)) 
     (S1_V4_!18 (_ BitVec 32)))
    (let
    (($x267
      (and (= (ite MW_S1_V4 S1_V4_!12 V4_0) (ite MW_S1_V4 S1_V4_!18 V4_0))
      (= E1_!16 (ite MW_S1_V1 S1_V1_!21 E1_!17))
      (= (ite MW_S1_V3 S1_V3_!14 V3_0) (ite MW_S1_V3 S1_V3_!20 V3_0))
      (= (ite MW_S1_V1 S1_V1_!15 E1_!11) (ite MW_S1_V1 S1_V1_!21 E1_!17)))))
    (let
    (($x297
      (and (or (not R_E1_V4) (= (ite MW_S1_V4 S1_V4_!12 V4_0) V4_0))
      (or (not R_E1_V2) (= (ite MW_S1_V2 S1_V2_!13 V2_0) V2_0))
      (or (not R_E1_V3) (= (ite MW_S1_V3 S1_V3_!14 V3_0) V3_0))
      (or (not R_E1_V1) (= (ite MW_S1_V1 S1_V1_!15 E1_!11) V1_0)))))
    (let
    (($x310
      (and (or (not R_E1_V4) (= V4_0 (ite MW_S1_V4 S1_V4_!12 V4_0)))
      (or (not R_E1_V2) (= V2_0 (ite MW_S1_V2 S1_V2_!13 V2_0)))
      (or (not R_E1_V3) (= V3_0 (ite MW_S1_V3 S1_V3_!14 V3_0)))
      (or (not R_E1_V1) (= V1_0 (ite MW_S1_V1 S1_V1_!15 E1_!11))))))
    (let
    (($x321
      (and
      (or (not (or (not R_S1_V1) (= E1_!17 E1_!11))) (= S1_V3_!20 S1_V3_!14))
      (or (not $x310) (= E1_!11 E1_!16)) 
      (= E1_!11 E1_!17) (or (not $x297) (= E1_!16 E1_!17))
      (or (not (or (not R_S1_V1) (= E1_!17 E1_!11))) (= S1_V1_!21 S1_V1_!15))
      (or (not (or (not R_S1_V1) (= E1_!17 E1_!11))) (= S1_V2_!19 S1_V2_!13))
      (or (not (or (not R_S1_V1) (= E1_!17 E1_!11))) (= S1_V4_!18 S1_V4_!12))
      (or (not MW_S1_V4) W_S1_V4) 
      (or (not MW_S1_V2) W_S1_V2) 
      (or (not MW_S1_V1) W_S1_V1)))) 
    (or (not $x321) $x267))))))))
 (let
 (($x40
   (or (and W_S1_V4 R_E1_V4) 
   (and W_S1_V2 R_E1_V2) R_E1_V3 
   (and W_S1_V1 R_E1_V1))))
 (let (($x42 (= DISJ_W_S1_R_E1 (not $x40))))
 (let
 (($x37
   (or (and W_S1_V4 R_S1_V4) 
   (and W_S1_V2 R_S1_V2) R_S1_V3 
   (and W_S1_V1 R_S1_V1))))
 (let (($x39 (= DISJ_W_S1_R_S1 (not $x37)))) (and W_S1_V3 $x39 $x42 $x324)))))))
(check-sat)
(exit)

